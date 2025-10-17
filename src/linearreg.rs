pub struct OnlineLinearRegression {
    weights: Vec<f64>,
    learning_rate: f64,
    l2_lambda: f64,
    clip_grad: Option<f64>,
}

impl OnlineLinearRegression {
    pub fn new(n_features: usize, learning_rate: f64) -> Self {
        Self { weights: vec![0.0; n_features + 1], learning_rate, l2_lambda: 0.0, clip_grad: None }
    }

    pub fn with_l2_regularization(mut self, lambda: f64) -> Self { self.l2_lambda = lambda; self }
    pub fn with_grad_clip(mut self, clip: f64) -> Self { self.clip_grad = Some(clip); self }

    pub fn predict(&self, features: &[f64]) -> f64 {
        debug_assert_eq!(features.len() + 1, self.weights.len());
        let mut s = self.weights[0];
        for (w, x) in self.weights[1..].iter().zip(features) { s += w * x; }
        s
    }

    pub fn partial_fit(&mut self, features: &[f64], target: f64) -> f64 {
        let y_hat = self.predict(features);
        let mut err = y_hat - target;
        if let Some(c) = self.clip_grad { if err > c { err = c } else if err < -c { err = -c } }

        self.weights[0] -= self.learning_rate * err;

        let decay = 1.0 - self.learning_rate * self.l2_lambda;
        for (w, x) in self.weights[1..].iter_mut().zip(features) {
            *w = *w * decay - self.learning_rate * err * x;
        }

        0.5 * err * err
    }

    pub fn weights(&self) -> &[f64] { &self.weights }
}
