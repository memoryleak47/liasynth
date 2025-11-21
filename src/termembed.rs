use crate::Term;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

pub struct TermEmbedder {
    embedding_dim: usize,
}

impl TermEmbedder {
    pub fn new(embedding_dim: usize) -> Self {
        assert!(embedding_dim > 0);
        Self { embedding_dim }
    }

    pub fn embed(&self, term: &Term) -> Vec<f64> {
        let mut vec = vec![0.0; self.embedding_dim];

        if term.elems.is_empty() {
            return vec;
        }

        let size = term.elems.len() as f64;

        for node in &term.elems {
            let mut hasher = DefaultHasher::new();
            node.hash(&mut hasher);
            let h = hasher.finish() as usize;

            let idx = h % self.embedding_dim;
            vec[idx] += 1.0;
        }

        for i in 0..self.embedding_dim {
            vec[i] /= size;
        }

        if self.embedding_dim > 1 {
            vec[self.embedding_dim - 1] = (size / 100.0).min(1.0);
        }

        vec
    }
}
