use std::collections::HashMap;
use std::hash::Hash;

#[derive(Debug, Clone)]
pub struct Env<'env, K, V> {
    parent: Option<&'env Env<'env, K, V>>,
    ctx: HashMap<K, V>,
}

impl<'env, K, V> Default for Env<'env, K, V> {
    fn default() -> Self {
        Self {
            parent: None,
            ctx: HashMap::new(),
        }
    }
}

impl<'env, K, V> Env<'env, K, V>
where
    K: Eq + Hash,
{
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_parent(parent: &'env Env<'env, K, V>) -> Self {
        Self {
            parent: Some(parent),
            ..Default::default()
        }
    }

    /// Inserts a mapping from key to value in the current environment.
    pub fn insert(&mut self, key: K, value: V) {
        self.ctx.insert(key, value);
    }

    /// Retrieves the value associated with key from the environment, if it is not
    /// present in the current one, it will try recursively with the parent environments
    /// until it is found, or the root is reached, in which case it returns None.
    pub fn get(&self, key: &K) -> Option<&V> {
        self.ctx.get(key).or_else(|| match self.parent {
            Some(p) => p.get(key),
            None => None,
        })
    }

    /// Retrieves the value associated with key from the current environment, if it is
    /// not present, it will return None. It will **not** try to search with the parent.
    pub fn get_immediate(&self, key: &K) -> Option<&V> {
        self.ctx.get(key)
    }
}
