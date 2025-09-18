// From the perceptron crate: https://docs.rs/perceptron/0.1.1/perceptron/


use crate::*;
use serde::{Serialize, Deserialize};

#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct Perceptron {
    weights: Vec<f32>,
    s_weights: Vec<f32>,
    n_examples: u32,
}

impl Perceptron {
    pub fn new(n_feats: usize) -> Perceptron {
        Perceptron{ weights: vec![0.0; n_feats + 1], s_weights: vec![0.0; n_feats + 1], n_examples: 0 }
    }

    pub fn train(&self, example: Vec<f32>, label: f32) -> Option<Perceptron>
    {
        if example.len() + 1 == self.weights.len() {
            let pexample: Vec<f32> = example.into_iter().chain(vec!(1.0).into_iter()).collect();
            let pred: f32 = self.weights.iter().zip(pexample.iter()).map(|(w, e)| w * e).sum();
            let flabel = if label {1.0} else {-1.0};

            if flabel * pred > 0.0 {
                return Some(Perceptron{weights: self.weights.clone(), s_weights: self.s_weights.clone(), n_examples: self.n_examples+1})
            }

            let update_vec: Vec<f32> = pexample.iter().map(|x| flabel * x).collect();
            return Some(Perceptron{weights: self.weights.iter().zip(update_vec.iter()).map(|(a,b)| a+b).collect(),
                                   s_weights: self.s_weights.iter().zip(update_vec.iter()).map(|(a,b)| (a+(self.n_examples as f32)*b).clone()).collect(),
                                   n_examples: self.n_examples + 1})
        }
        None
    }

    pub fn predict(&self, feats: Vec<f32>) -> f32 {
        let pfeats: Vec<f32> = feats.into_iter().chain(vec!(1.0).into_iter()).collect();
        let temp: Vec<f32> = self.s_weights.iter().map(|w| (w / (self.n_examples as f32))).collect();
        let weights: Vec<f32> = self.weights.iter().zip(temp.iter()).map(|(a,b)| a-b).collect();
        let pred: f32 = weights.iter().zip(pfeats.iter()).map(|(w, e)| w * e).sum();
        pred
    }
}


pub fn feature_set1(x: Id, ctxt: &Ctxt) -> Vec<f32> {
    todo!();
}
