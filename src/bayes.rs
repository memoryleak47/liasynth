use nalgebra::{DMatrix, DVector};

pub struct BayesianLinearRegression {
    degree: usize,
    beta: f64,    // 1 / noise_var
    d: usize,     // degree + 1
    s_inv: DMatrix<f64>,
    m: DVector<f64>,
}

impl BayesianLinearRegression {
    pub fn new(degree: usize, noise_var: f64, prior_var: f64) -> Self {
        let beta = 1.0 / noise_var;
        let alpha = 1.0 / prior_var;
        let d = degree + 1;

        // Create identity matrix multiplied by alpha
        let s_inv = DMatrix::identity(d, d) * alpha;

        // Create zero vector
        let m = DVector::zeros(d);

        Self {
            degree,
            beta,
            d,
            s_inv,
            m,
        }
    }

    fn polynomial_features(&self, x: &DMatrix<f64>) -> DMatrix<f64> {
        let n_samples = x.nrows();

        // Create feature matrix with ones in first column
        let mut features = DMatrix::zeros(n_samples, self.d);

        // First column is all ones
        features.set_column(0, &DVector::repeat(n_samples, 1.0));

        // Add polynomial features
        for degree in 1..=self.degree {
            for i in 0..n_samples {
                let row_sum: f64 = x.row(i).iter().map(|&val| val.powi(degree as i32)).sum();
                features[(i, degree)] = row_sum;
            }
        }

        features
    }

    pub fn update(&mut self, x: &DMatrix<f64>, y: &DVector<f64>) -> Result<(), String> {
        let x_features = self.polynomial_features(x);
        let n_samples = x_features.nrows();

        // Ensure y has correct length
        if y.len() != n_samples {
            return Err(format!("y length {} doesn't match number of samples {}", y.len(), n_samples));
        }

        // Update inverse covariance: S_inv_new = S_prev_inv + beta * (X.T @ X)
        let xtx = x_features.transpose() * &x_features;
        let s_inv_new = &self.s_inv + self.beta * xtx;

        // Solve for new mean: S_inv_new * m_new = S_prev_inv * m_prev + beta * X.T * y
        let rhs = &self.s_inv * &self.m + self.beta * x_features.transpose() * y;

        // Use LU decomposition to solve the linear system
        let m_new = s_inv_new.clone().lu().solve(&rhs)
            .ok_or_else(|| "Failed to solve linear system - matrix might be singular".to_string())?;

        // Update state
        self.s_inv = s_inv_new;
        self.m = m_new;

        Ok(())
    }

    pub fn predict(&self, x: &DMatrix<f64>) -> Result<(DVector<f64>, DVector<f64>), String> {
        let x_features = self.polynomial_features(x);           // X: (n × d)

        // Mean: X m
        let mean = &x_features * &self.m;                       // (n × 1)

        // Solve S_inv * Z = X^T  ⇒  Z = S * X^T  (d × n) without forming S explicitly
        let xt = x_features.transpose();                        // (d × n)
        let z = self.s_inv.clone().lu().solve(&xt)
            .ok_or_else(|| "Failed to solve for S * X^T (singular S_inv)".to_string())?; // (d × n)

        // X * Z = X * (S * X^T) ⇒ n × n; take diagonal to get diag(X S X^T)
        let gram = &x_features * z;                             // (n × n)
        let mut variances = gram.diagonal().into_owned();       // (n × 1)
        variances.add_scalar_mut(1.0 / self.beta);              // + noise variance

        let std = variances.map(|v| v.sqrt());                  // elementwise sqrt
        Ok((mean, std))
    }

    // Convenience methods for 1D inputs (common case)
    pub fn update_1d(&mut self, x: &[f64], y: &[f64]) -> Result<(), String> {
        if x.len() != y.len() {
            return Err("x and y must have the same length".to_string());
        }

        let x_matrix = DMatrix::from_column_slice(x.len(), 1, x);
        let y_vector = DVector::from_column_slice(y);
        self.update(&x_matrix, &y_vector)
    }

    pub fn predict_1d(&self, x: &[f64]) -> Result<(Vec<f64>, Vec<f64>), String> {
        let x_matrix = DMatrix::from_column_slice(x.len(), 1, x);
        let (mean, std) = self.predict(&x_matrix)?;
        Ok((mean.data.into(), std.data.into()))
    }
}
