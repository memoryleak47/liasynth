use crate::Term;
use std::collections::HashMap;


pub struct TermEmbedder {
    template_to_idx: HashMap<String, usize>,
    embedding_dim: usize,
}

impl TermEmbedder {
    pub fn new(embedding_dim: usize) -> Self {
        Self { 
            template_to_idx: HashMap::new(),
            embedding_dim 
        }
    }

    pub fn embed(&mut self, term: &Term) -> Vec<f64> {
        let mut vec = vec![0.0; self.embedding_dim];

        if term.elems.is_empty() {
            return vec;
        }

        let mut counts = HashMap::new();
        for node in &term.elems {

            let key = node.template()
                .map(|s| s.to_string())
                .unwrap_or_else(|| format!("{:?}", std::mem::discriminant(node)));

            if !self.template_to_idx.contains_key(&key) {
                self.template_to_idx.insert(key.clone(), self.template_to_idx.len());
            }

            let idx = self.template_to_idx[&key];
            *counts.entry(idx).or_insert(0.0) += 1.0;
        }

        let size = term.elems.len() as f64;
        for count in counts.values_mut() {
            *count /= size;
        }

        for (idx, count) in counts {
            let target = idx % self.embedding_dim;
            vec[target] += count;
        }

        if self.embedding_dim > 1 {
            vec[self.embedding_dim - 1] = (size / 100.0).min(1.0);
        }

        vec
    }

    pub fn vocab_size(&self) -> usize {
        self.template_to_idx.len()
    }
}
