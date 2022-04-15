use std::collections::HashMap;
use std::hash::Hash;

#[derive(Debug)]
pub struct Env<'parent, K, V> {
    mapping: HashMap<K, V>,
    parent: Option<&'parent Env<'parent, K, V>>,
}

impl<'parent, K, V> Default for Env<'parent, K, V> {
    fn default() -> Self {
        Self {
            mapping: HashMap::new(),
            parent: None,
        }
    }
}

impl<'parent, K, V> Env<'parent, K, V>
where
    K: Eq + Hash,
{
    /// Creates a new root environment.
    pub fn new() -> Self {
        Self::default()
    }

    /// Creates a new child environment, which points to the current one.
    pub fn new_child(&'parent self) -> Self {
        Self {
            parent: Some(self),
            ..Default::default()
        }
    }

    /// Looks up `key` recursively inside the environment.
    pub fn look(&self, key: &K) -> Option<&V> {
        self.mapping.get(key).or_else(|| match self.parent {
            Some(p) => p.look(key),
            None => None,
        })
    }

    /// Inserts the mapping `key` -> `value` into the current environment.
    pub fn enter(&mut self, key: K, value: V) {
        self.mapping.insert(key, value);
    }

    /// Similar to `look`, but only looks in the current environment, ignorint the parent, if any.
    pub fn get_immediate(&mut self, key: &K) -> Option<&V> {
        self.mapping.get(key)
    }
}
