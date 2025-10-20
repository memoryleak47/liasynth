use std::ops::{Add, Mul};

pub struct BayesianLinearRegression {
    n_features: usize,
    mu: Vec<f64>,
    v_inv: Vec<Vec<f64>>,
    a: f64,
    b: f64,
    n_obs: usize,
}

impl BayesianLinearRegression {
    pub fn new(n_features: usize, prior_variance: f64, noise_shape: f64, noise_scale: f64) -> Self {
        let dim = n_features + 1;
        let mu = vec![0.0; dim];
        let mut v_inv = vec![vec![0.0; dim]; dim];
        let prior_precision = 1.0 / prior_variance;
        for i in 0..dim {
            v_inv[i][i] = prior_precision;
        }

        Self {
            n_features,
            mu,
            v_inv,
            a: noise_shape,
            b: noise_scale,
            n_obs: 0,
        }
    }

    pub fn with_default_prior(n_features: usize) -> Self {
        Self::new(
            n_features,
            100.0,
            1.0,
            1.0,
        )
    }


    pub fn predict(&self, features: &[f64]) -> (f64, f64) {
        debug_assert_eq!(features.len(), self.n_features);

        let x = self.build_feature_vector(features);

        let mean = dot(&x, &self.mu);

        let sigma_sq = self.b / self.a;
        let v = self.compute_v();
        let xvx = quadratic_form(&x, &v);
        let variance = sigma_sq * (1.0 + xvx);

        (mean, variance)
    }

    pub fn predict_mean(&self, features: &[f64]) -> f64 {
        self.predict(features).0
    }

    pub fn update(&mut self, features: &[f64], target: f64) -> f64 {
        debug_assert_eq!(features.len(), self.n_features);

        let x = self.build_feature_vector(features);

        let (pred_mean, pred_var) = self.predict(features);
        let error = target - pred_mean;

        for i in 0..self.v_inv.len() {
            for j in 0..self.v_inv[0].len() {
                self.v_inv[i][j] += x[i] * x[j];
            }
        }

        let v_inv_mu = matvec(&self.v_inv, &self.mu);

        let mut rhs = vec![0.0; self.mu.len()];
        for i in 0..rhs.len() {
            rhs[i] = v_inv_mu[i] + target * x[i] - x[i] * x[i] * self.mu[i];
        }

        self.mu = sherman_morrison_solve(&self.v_inv, &x, &self.mu, target);

        self.a += 0.5;

        let v_old = self.compute_v_before_update(&x);
        let xvx_old = quadratic_form(&x, &v_old);
        let residual = target - dot(&x, &self.mu);
        self.b += 0.5 * residual * residual / (1.0 + xvx_old);

        self.n_obs += 1;

        0.5 * (pred_var.ln() + error * error / pred_var)
    }

    pub fn weights(&self) -> &[f64] {
        &self.mu
    }

    pub fn weight_variances(&self) -> Vec<f64> {
        let v = self.compute_v();
        let sigma_sq = self.b / self.a;
        (0..v.len()).map(|i| sigma_sq * v[i][i]).collect()
    }

    pub fn noise_variance(&self) -> f64 {
        self.b / self.a
    }

    pub fn n_observations(&self) -> usize {
        self.n_obs
    }

    fn build_feature_vector(&self, features: &[f64]) -> Vec<f64> {
        let mut x = Vec::with_capacity(self.n_features + 1);
        x.push(1.0); // Bias term
        x.extend_from_slice(features);
        x
    }

    fn compute_v(&self) -> Vec<Vec<f64>> {
        invert_matrix(&self.v_inv)
    }

    fn compute_v_before_update(&self, x: &[f64]) -> Vec<Vec<f64>> {
        let mut v_inv_old = self.v_inv.clone();
        for i in 0..v_inv_old.len() {
            for j in 0..v_inv_old[0].len() {
                v_inv_old[i][j] -= x[i] * x[j];
            }
        }
        invert_matrix(&v_inv_old)
    }
}

fn dot(a: &[f64], b: &[f64]) -> f64 {
    a.iter().zip(b).map(|(x, y)| x * y).sum()
}

fn matvec(a: &[Vec<f64>], x: &[f64]) -> Vec<f64> {
    a.iter().map(|row| dot(row, x)).collect()
}

fn quadratic_form(x: &[f64], a: &[Vec<f64>]) -> f64 {
    // Compute x^T * A * x
    let ax = matvec(a, x);
    dot(x, &ax)
}

fn sherman_morrison_solve(
    v_inv: &[Vec<f64>],
    x_obs: &[f64],
    mu_old: &[f64],
    y: f64,
) -> Vec<f64> {
    let n = mu_old.len();
    let v = invert_matrix(v_inv);
    let mut rhs = matvec(v_inv, mu_old);
    for i in 0..n {
        rhs[i] += y * x_obs[i];
    }
    matvec(&v, &rhs)
}

fn invert_matrix(a: &[Vec<f64>]) -> Vec<Vec<f64>> {
    let n = a.len();
    let mut aug = vec![vec![0.0; 2 * n]; n];

    for i in 0..n {
        for j in 0..n {
            aug[i][j] = a[i][j];
        }
        aug[i][n + i] = 1.0;
    }

    for i in 0..n {
        let mut max_row = i;
        for k in (i + 1)..n {
            if aug[k][i].abs() > aug[max_row][i].abs() {
                max_row = k;
            }
        }
        aug.swap(i, max_row);

        let diag = aug[i][i];
        for j in 0..(2 * n) {
            aug[i][j] /= diag;
        }

        for k in 0..n {
            if k != i {
                let factor = aug[k][i];
                for j in 0..(2 * n) {
                    aug[k][j] -= factor * aug[i][j];
                }
            }
        }
    }

    let mut inv = vec![vec![0.0; n]; n];
    for i in 0..n {
        for j in 0..n {
            inv[i][j] = aug[i][n + j];
        }
    }
    inv
}
