use crate::Child;
use crate::Term;

pub struct TermEmbedder {
    embedding_dim: usize,
}

impl TermEmbedder {
    pub fn new(embedding_dim: usize) -> Self {
        assert!(embedding_dim >= 3);
        Self { embedding_dim }
    }

    pub fn embed(&self, term: &Term) -> Vec<f64> {
        let mut vec = vec![0.0; self.embedding_dim];

        let n = term.elems.len();
        if n == 0 {
            return vec;
        }

        let mut has_parent = vec![false; n];
        for node in term.elems.iter() {
            for &child in node.children() {
                if let Child::Hole(_, i) = child {
                    has_parent[i] = true;
                }
            }
        }
        let root = has_parent.iter().position(|&p| !p).unwrap_or(n - 1);

        let mut stack = vec![(root, 0usize)];
        let mut depths = vec![0usize; n];
        let mut max_depth = 0usize;
        let mut total_children = 0usize;
        let mut leaf_count = 0usize;

        while let Some((idx, d)) = stack.pop() {
            depths[idx] = d;
            if d > max_depth {
                max_depth = d;
            }
            let node = &term.elems[idx];
            let children = node.children();
            let arity = children.len();
            total_children += arity;
            if arity == 0 {
                leaf_count += 1;
            }
            for &c in children {
                if let Child::Hole(_, i) = c {
                    stack.push((i, d + 1));
                }
            }
        }

        let size = n as f64;
        let avg_branching = total_children as f64 / size;
        let leaf_ratio = leaf_count as f64 / size;

        let hist_bins = self.embedding_dim - 2;
        if hist_bins > 0 {
            if max_depth == 0 {
                vec[0] = 1.0;
            } else {
                for d in depths {
                    let bin = if d >= max_depth {
                        hist_bins - 1
                    } else {
                        d * hist_bins / (max_depth.max(1))
                    };
                    vec[bin] += 1.0;
                }
                for i in 0..hist_bins {
                    vec[i] /= size;
                }
            }
        }

        if self.embedding_dim >= 2 {
            let size_feature = (size / 100.0).min(1.0);
            let shape_feature = ((avg_branching + leaf_ratio) / 5.0).min(1.0);
            vec[self.embedding_dim - 2] = size_feature;
            vec[self.embedding_dim - 1] = shape_feature;
        }

        vec
    }
}
