use std::ops::{Add, Mul};

pub struct BayesianLinearRegression {
    n_features: usize,
    mu: Vec<f64>,
    v: Vec<Vec<f64>>, // Covariance matrix (not inverse!)
    a: f64,
    b: f64,
    n_obs: usize,
}

impl BayesianLinearRegression {
    pub fn new(n_features: usize, prior_variance: f64, noise_shape: f64, noise_scale: f64) -> Self {
        let dim = n_features + 1;
        let mu = vec![0.0; dim];

        // Initialize V (covariance) as diagonal with prior variance
        let mut v = vec![vec![0.0; dim]; dim];
        for i in 0..dim {
            v[i][i] = prior_variance;
        }

        Self {
            n_features,
            mu,
            v,
            a: noise_shape,
            b: noise_scale,
            n_obs: 0,
        }
    }

    pub fn with_default_prior(n_features: usize) -> Self {
        Self::new(n_features, 100.0, 1.0, 1.0)
    }

    pub fn predict(&self, features: &[f64]) -> (f64, f64) {
        debug_assert_eq!(features.len(), self.n_features);

        let x = self.build_feature_vector(features);

        let mean = dot(&x, &self.mu);

        let sigma_sq = self.b / self.a;
        let xvx = quadratic_form(&x, &self.v);
        let variance = sigma_sq * (1.0 + xvx);

        (mean, variance)
    }

    pub fn predict_mean(&self, features: &[f64]) -> f64 {
        self.predict(features).0
    }

    pub fn update(&mut self, features: &[f64], target: f64, num_cxs: usize) -> f64 {
        debug_assert_eq!(features.len(), self.n_features);

        let target = if num_cxs > 0 {
            (target / num_cxs as f64).min(1.0)
        } else {
            0.0
        };

        let x = self.build_feature_vector(features);

        // Compute prediction BEFORE update for log-likelihood
        let (pred_mean, pred_var) = self.predict(features);
        let error = target - pred_mean;

        // Store old values for noise update
        let sigma_sq = self.b / self.a;
        let xvx = quadratic_form(&x, &self.v);

        // Update mean using current V
        // New posterior mean: mu_new = mu + V*x*(y - x^T*mu) / (sigma^2 + x^T*V*x)
        let vx = matvec(&self.v, &x);
        let denominator = sigma_sq + xvx;
        let gain = 1.0 / denominator;

        for i in 0..self.mu.len() {
            self.mu[i] += gain * error * vx[i];
        }

        // Sherman-Morrison update for V
        // V_new = V - (V*x)(V*x)^T / (sigma^2 + x^T*V*x)
        for i in 0..self.v.len() {
            for j in 0..self.v[0].len() {
                self.v[i][j] -= (vx[i] * vx[j]) * gain;
            }
        }

        // Update noise parameters
        self.a += 0.5;
        self.b += 0.5 * error * error / (1.0 + xvx / sigma_sq);

        self.n_obs += 1;

        // Return negative log predictive density
        0.5 * (pred_var.ln() + error * error / pred_var)
    }

    pub fn weights(&self) -> &[f64] {
        &self.mu
    }

    pub fn weight_variances(&self) -> Vec<f64> {
        let sigma_sq = self.b / self.a;
        (0..self.v.len()).map(|i| sigma_sq * self.v[i][i]).collect()
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
}

// Helper functions

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
