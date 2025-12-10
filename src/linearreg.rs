use rand::SeedableRng;
use rand_distr::Distribution;
use rand_distr::{Normal, Uniform};

pub struct Rff {
    w: Vec<Vec<f64>>,
    b: Vec<f64>,
    scale: f64,
    pub num_features: usize,
}

impl Rff {
    pub fn new(input_dim: usize, num_features: usize, sigma: f64, seed: u64) -> Self {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let normal = Normal::new(0.0, 1.0 / sigma).unwrap();
        let uniform = Uniform::new(0.0, 2.0 * std::f64::consts::PI).unwrap();

        let mut w = Vec::with_capacity(num_features);
        let mut b = Vec::with_capacity(num_features);

        for _ in 0..num_features {
            let wi = (0..input_dim).map(|_| normal.sample(&mut rng)).collect();
            w.push(wi);
            b.push(uniform.sample(&mut rng));
        }

        Self {
            w,
            b,
            scale: (2.0 / num_features as f64).sqrt(),
            num_features,
        }
    }

    pub fn transform(&self, x: &[f64]) -> Vec<f64> {
        self.w
            .iter()
            .zip(self.b.iter())
            .map(|(wi, bi)| {
                let dot = wi.iter().zip(x).map(|(a, b)| a * b).sum::<f64>();
                self.scale * (dot + bi).cos()
            })
            .collect()
    }
}

pub struct BayesianLinearRegression {
    mu: Vec<f64>,
    v: Vec<Vec<f64>>,
    sigma_sq: f64,
    lambda_prior: f64,
    eta_lik: f64,
    n_obs: usize,
    pub rff: Rff,
}

impl BayesianLinearRegression {
    pub fn new(
        input_dim: usize,
        rff_features: usize,
        sigma_rff: f64,
        seed: u64,
        prior_variance: f64,
        noise_variance: f64,
        lambda_prior: f64,
        eta_lik: f64,
    ) -> Self {
        let rff = Rff::new(input_dim, rff_features, sigma_rff, seed);
        let dim = rff.num_features + 1;

        let mut v = vec![vec![0.0; dim]; dim];
        for i in 0..dim {
            v[i][i] = prior_variance;
        }

        Self {
            mu: vec![0.0; dim],
            v,
            sigma_sq: noise_variance,
            lambda_prior: lambda_prior.clamp(0.0001, 1.0),
            eta_lik: eta_lik.max(1e-6),
            n_obs: 0,
            rff,
        }
    }

    pub fn with_default(input_dim: usize, rff_features: usize) -> Self {
        BayesianLinearRegression::new(input_dim, rff_features, 1.0, 12345, 100.0, 1.0, 0.99, 1.0)
    }

    fn build_feature_vector(&self, x_raw: &[f64]) -> Vec<f64> {
        let mut out = Vec::with_capacity(self.mu.len());
        out.push(1.0);
        out.extend(self.rff.transform(x_raw));
        out
    }

    pub fn predict(&self, x_raw: &[f64]) -> (f64, f64) {
        let x = self.build_feature_vector(x_raw);
        let mean = dot(&x, &self.mu);
        let xvx = quadratic_form(&x, &self.v);
        let var = self.sigma_sq + xvx;
        (mean, var)
    }

    pub fn predict_mean(&self, x_raw: &[f64]) -> f64 {
        self.predict(x_raw).0
    }

    pub fn predict_std(&self, x_raw: &[f64]) -> f64 {
        self.predict(x_raw).1.sqrt()
    }

    pub fn update(&mut self, x_raw: &[f64], y: f64) -> f64 {
        let x = self.build_feature_vector(x_raw);

        if self.lambda_prior < 1.0 {
            let inv_lambda = 1.0 / self.lambda_prior;
            for i in 0..self.v.len() {
                for j in 0..self.v[0].len() {
                    self.v[i][j] *= inv_lambda;
                }
            }
        }

        let vx = matvec(&self.v, &x);
        let xvx = dot(&x, &vx);

        let adj_sigma_sq = self.sigma_sq / self.eta_lik;
        let denom = adj_sigma_sq + xvx;
        let gain = 1.0 / denom;

        let pred = dot(&x, &self.mu);
        let error = y - pred;

        let scaled_gain = self.eta_lik * gain;

        for i in 0..self.mu.len() {
            self.mu[i] += scaled_gain * error * vx[i];
        }

        for i in 0..self.v.len() {
            for j in 0..self.v[0].len() {
                self.v[i][j] -= scaled_gain * vx[i] * vx[j];
            }
        }

        self.n_obs += 1;

        0.5 * error * error
    }
}

fn dot(a: &[f64], b: &[f64]) -> f64 {
    a.iter().zip(b).map(|(x, y)| x * y).sum()
}

fn matvec(a: &[Vec<f64>], x: &[f64]) -> Vec<f64> {
    a.iter().map(|row| dot(row, x)).collect()
}

fn quadratic_form(x: &[f64], a: &[Vec<f64>]) -> f64 {
    dot(x, &matvec(a, x))
}
