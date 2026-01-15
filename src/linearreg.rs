// use rand::{Rng, SeedableRng};
// use rand_distr::Distribution;
// use rand_distr::{Normal, Uniform};
// 
// pub struct Rff {
//     w: Vec<Vec<f64>>,
//     b: Vec<f64>,
//     scale: f64,
//     pub num_features: usize,
// }
// 
// impl Rff {
//     pub fn new(input_dim: usize, num_features: usize, sigma: f64, seed: u64) -> Self {
//         let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
//         let normal = Normal::new(0.0, 1.0 / sigma).unwrap();
//         let uniform = Uniform::new(0.0, 2.0 * std::f64::consts::PI).unwrap();
// 
//         let mut w = Vec::with_capacity(num_features);
//         let mut b = Vec::with_capacity(num_features);
// 
//         for _ in 0..num_features {
//             let wi = (0..input_dim).map(|_| normal.sample(&mut rng)).collect();
//             w.push(wi);
//             b.push(uniform.sample(&mut rng));
//         }
// 
//         Self {
//             w,
//             b,
//             scale: (2.0 / num_features as f64).sqrt(),
//             num_features,
//         }
//     }
// 
//     pub fn transform(&self, x: &[f64]) -> Vec<f64> {
//         self.w
//             .iter()
//             .zip(self.b.iter())
//             .map(|(wi, bi)| {
//                 let dot = wi.iter().zip(x).map(|(a, b)| a * b).sum::<f64>();
//                 self.scale * (dot + bi).cos()
//             })
//             .collect()
//     }
// }
// 
// pub struct BayesianLinearRegression {
//     mu: Vec<f64>,
//     v: Vec<Vec<f64>>,
//     a: f64,
//     b: f64,
//     n_obs: usize,
// 
//     pub rff: Rff,
// }
// 
// impl BayesianLinearRegression {
//     pub fn new(
//         input_dim: usize,
//         rff_features: usize,
//         sigma: f64,
//         seed: u64,
//         prior_variance: f64,
//         noise_shape: f64,
//         noise_scale: f64,
//     ) -> Self {
//         let rff = Rff::new(input_dim, rff_features, sigma, seed);
//         let dim = rff.num_features + 1;
// 
//         let mut v = vec![vec![0.0; dim]; dim];
//         for i in 0..dim {
//             v[i][i] = prior_variance;
//         }
// 
//         Self {
//             mu: vec![0.0; dim],
//             v,
//             a: noise_shape,
//             b: noise_scale,
//             n_obs: 0,
//             rff,
//         }
//     }
// 
//     pub fn with_default(input_dim: usize, rff_features: usize) -> Self {
//         Self::new(input_dim, rff_features, 1.0, 12345, 100.0, 1.0, 1.0)
//     }
// 
//     pub fn predict(&self, x_raw: &[f64]) -> (f64, f64) {
//         let x = self.build_feature_vector(x_raw);
// 
//         let mean = dot(&x, &self.mu);
//         let sigma_sq = self.b / self.a;
// 
//         let xvx = quadratic_form(&x, &self.v);
//         let var = sigma_sq * (1.0 + xvx);
// 
//         (mean, var)
//     }
// 
//     pub fn predict_mean(&self, x_raw: &[f64]) -> f64 {
//         self.predict(x_raw).0
//     }
// 
//     pub fn predict_std(&self, x_raw: &[f64]) -> f64 {
//         self.predict(x_raw).1.sqrt()
//     }
// 
//     pub fn update(&mut self, x_raw: &[f64], y: f64) -> f64 {
//         let x = self.build_feature_vector(x_raw);
// 
//         let (pred_mean, pred_var) = self.predict(x_raw);
//         let error = y - pred_mean;
//         let sigma_sq = self.b / self.a;
//         let xvx = quadratic_form(&x, &self.v);
// 
//         let vx = matvec(&self.v, &x);
//         let denom = sigma_sq + xvx;
//         let gain = 1.0 / denom;
// 
//         for i in 0..self.mu.len() {
//             self.mu[i] += gain * error * vx[i];
//         }
// 
//         for i in 0..self.v.len() {
//             for j in 0..self.v[0].len() {
//                 self.v[i][j] -= vx[i] * vx[j] * gain;
//             }
//         }
// 
//         self.a += 0.5;
//         let noise_update = 0.5 * error * error / (1.0 + xvx / sigma_sq);
//         self.b = (self.b + noise_update).clamp(0.01, 1000.0);
// 
//         self.n_obs += 1;
// 
//         0.5 * (pred_var.ln() + error * error / pred_var)
//     }
// 
//     fn build_feature_vector(&self, x_raw: &[f64]) -> Vec<f64> {
//         let mut out = Vec::with_capacity(self.mu.len());
//         out.push(1.0); // bias
//         out.extend(self.rff.transform(x_raw));
//         out
//     }
// }
// 
// fn dot(a: &[f64], b: &[f64]) -> f64 {
//     a.iter().zip(b).map(|(x, y)| x * y).sum()
// }
// 
// fn matvec(a: &[Vec<f64>], x: &[f64]) -> Vec<f64> {
//     a.iter().map(|row| dot(row, x)).collect()
// }
// 
// fn quadratic_form(x: &[f64], a: &[Vec<f64>]) -> f64 {
//     dot(x, &matvec(a, x))
// }
//



use rand::{Rng, SeedableRng};
use rand_distr::{Distribution, Normal, Uniform};

use faer::{Mat, linalg::matmul::matmul, ColMut, ColRef, MatRef};


pub struct Rff {
    // Flat row-major: num_features x input_dim
    w: Vec<f64>,
    b: Vec<f64>,
    scale: f64,
    input_dim: usize,
    pub num_features: usize,
}

impl Rff {
    pub fn new(input_dim: usize, num_features: usize, sigma: f64, seed: u64) -> Self {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let normal = Normal::new(0.0, 1.0 / sigma).unwrap();
        let uniform = Uniform::new(0.0, 2.0 * std::f64::consts::PI).unwrap();

        let mut w = vec![0.0; num_features * input_dim];
        let mut b = vec![0.0; num_features];

        for j in 0..num_features {
            b[j] = uniform.sample(&mut rng);
            let off = j * input_dim;
            for i in 0..input_dim {
                w[off + i] = normal.sample(&mut rng);
            }
        }

        Self {
            w,
            b,
            scale: (2.0 / num_features as f64).sqrt(),
            input_dim,
            num_features,
        }
    }

    #[inline(always)]
    pub fn transform_into(&self, x: &[f64], out: &mut [f64]) {
        debug_assert_eq!(x.len(), self.input_dim);
        debug_assert_eq!(out.len(), self.num_features);

        // Hot loop. Still manual because RFF is a bunch of dot products; faer helps more on V updates.
        for j in 0..self.num_features {
            let off = j * self.input_dim;
            let mut dot = 0.0;
            for i in 0..self.input_dim {
                dot += self.w[off + i] * x[i];
            }
            out[j] = self.scale * (dot + self.b[j]).cos();
        }
    }
}

pub struct BayesianLinearRegression {
    // parameters
    mu: Vec<f64>, // length dim
    v: Mat<f64>,  // dim x dim

    a: f64,
    b: f64,
    n_obs: usize,

    pub rff: Rff,

    // scratch (no allocations in predict/update)
    x_feat: Vec<f64>, // length dim
    vx: Vec<f64>,     // length dim
}

impl BayesianLinearRegression {
    pub fn new(
        input_dim: usize,
        rff_features: usize,
        sigma: f64,
        seed: u64,
        prior_variance: f64,
        noise_shape: f64,
        noise_scale: f64,
    ) -> Self {
        let rff = Rff::new(input_dim, rff_features, sigma, seed);
        let dim = rff.num_features + 1;

        let mut v = Mat::<f64>::zeros(dim, dim);
        for i in 0..dim {
            v[(i, i)] = prior_variance;
        }

        Self {
            mu: vec![0.0; dim],
            v,
            a: noise_shape,
            b: noise_scale,
            n_obs: 0,
            rff,
            x_feat: vec![0.0; dim],
            vx: vec![0.0; dim],
        }
    }

    pub fn with_default(input_dim: usize, rff_features: usize) -> Self {
        Self::new(input_dim, rff_features, 1.0, 12345, 100.0, 1.0, 1.0)
    }

    #[inline(always)]
    fn build_feature_into(&mut self, x_raw: &[f64]) {
        self.x_feat[0] = 1.0;
        self.rff.transform_into(x_raw, &mut self.x_feat[1..]);
    }

    #[inline(always)]
    fn dot(a: &[f64], b: &[f64]) -> f64 {
        debug_assert_eq!(a.len(), b.len());
        // tight loop, no iterator overhead
        let mut s = 0.0;
        for i in 0..a.len() {
            s += a[i] * b[i];
        }
        s
    }

    #[inline(always)]
    fn matvec_faer(v: MatRef<'_, f64>, x: &[f64], out: &mut [f64]) {
        let n = x.len();
        debug_assert_eq!(v.nrows(), n);
        debug_assert_eq!(v.ncols(), n);
        debug_assert_eq!(out.len(), n);

        // Create column views using from_ref and from_mut
        let x_col: ColRef<'_, f64> = faer::col::from_slice(x);
        let mut y_col: ColMut<'_, f64> = faer::col::from_slice_mut(out);

        // matmul now takes 6 arguments: dst, lhs, rhs, alpha (Option<f64>), beta, parallelism
        use faer::Parallelism;
        matmul(
            y_col.as_2d_mut(),      // (n×1)
            v,                       // (n×n)
            x_col.as_2d(),          // (n×1)
            Some(1.0),              // alpha (wrapped in Some)
            0.0,                    // beta
            Parallelism::None,      // or Parallelism::Rayon(0) for parallel
        );
    }

    #[inline(always)]
    fn quadratic_form_from_vx(x: &[f64], vx: &[f64]) -> f64 {
        Self::dot(x, vx)
    }

    pub fn predict(&mut self, x_raw: &[f64]) -> (f64, f64) {
        self.build_feature_into(x_raw);
        let x = &self.x_feat[..];

        let mean = Self::dot(x, &self.mu);

        Self::matvec_faer(self.v.as_ref(), x, &mut self.vx);
        let xvx = Self::dot(x, &self.vx);

        let sigma_sq = self.b / self.a;
        let var = sigma_sq * (1.0 + xvx);

        (mean, var)
    }

    pub fn predict_mean(&mut self, x_raw: &[f64]) -> f64 {
        self.predict(x_raw).0
    }

    pub fn predict_std(&mut self, x_raw: &[f64]) -> f64 {
        self.predict(x_raw).1.sqrt()
    }

    pub fn update(&mut self, x_raw: &[f64], y: f64) -> f64 {
        self.build_feature_into(x_raw);
        let x = &self.x_feat[..];

        let pred_mean = Self::dot(x, &self.mu);

        Self::matvec_faer(self.v.as_ref(), x, &mut self.vx);
        let xvx = Self::dot(x, &self.vx);

        let sigma_sq = self.b / self.a;
        let pred_var = sigma_sq * (1.0 + xvx);

        let error = y - pred_mean;

        let denom = sigma_sq + xvx;
        let gain = 1.0 / denom;

        // mu += gain * error * vx
        let k = gain * error;
        for i in 0..self.mu.len() {
            self.mu[i] += k * self.vx[i];
        }

        // V -= gain * (vx outer vx)
        let n = self.mu.len();
        for i in 0..n {
            let vxi = self.vx[i];
            for j in 0..n {
                self.v[(i, j)] -= gain * vxi * self.vx[j];
            }
        }

        self.a += 0.5;
        let noise_update = 0.5 * error * error / (1.0 + xvx / sigma_sq);
        self.b = (self.b + noise_update).clamp(0.01, 1000.0);

        self.n_obs += 1;

        0.5 * (pred_var.ln() + error * error / pred_var)
    }
}
