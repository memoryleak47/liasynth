pub use egg::*;

mod core;
pub use core::*;

mod g;
pub use g::*;

pub type Map<K, V> = indexmap::IndexMap<K, V>;

fn main() {
}
