/*!
 * A compressed prefix tree implementation.
 *
 * Accepted keys are any type with slices that implement Eq.
 * Accepted values are anything that the tree can own.
 *
 * It is recommended to use static sized numbers or strings. Use `u8` if
 * string keys are being used.
 * 
 * Using the Trie with strings requires using the designated string
 * functions; this will automatically turn the string into a slice of 
 * u8's which is compatible with the tree. Unicode equivalency is not
 * checked.
 * 
 * It is not recommended to use the Trie with large structs as the key,
 * as performance will suffer due to the key being cloned into the prefix
 * tree, as opposed to referenced or taken into ownership.
 * 
 * Some unimplemented todos include:
 * - Add support for iteration
 * - Add support for in-place iteration, without IntoIter
 * 
 * In-place iteration without requiring the usage of Rc's or unsafe will likely be difficult due to the
 * tree's unidirectional nature.
 */

#![forbid(unsafe_code, missing_docs, missing_debug_implementations)]

cfg_if::cfg_if! {
    if #[cfg(feature ="std")] {
        extern crate std;
        use std::vec::Vec;
    }
    else {
        extern crate alloc;
        use alloc::vec::Vec;
    }
}

#[derive(Debug)]
/// Error returned if attempting to set a key with try_set, and the key already exists.
pub struct KeyExistsError;

#[derive(Debug)]
/// Error returned if attempting to remove a key that does not exist.
pub struct KeyNotFoundError;

/// compressed prefix tree
///
/// holds arbitrary values, uses string keys
/// common slices of stored keys are compressed by
/// not storing duplicates of those common slices.
#[derive(Debug, PartialEq, Eq)]
pub struct Trie<K: Eq + Clone, V> {
    /// tree root
    /// this will always be a node with the empty string.
    root: TrieNode<K, V>,
}

#[derive(Debug, PartialEq, Eq)]
struct TrieNode<K: Eq + Clone, V> {
    children: Vec<TrieNode<K, V>>,
    value: Option<V>,
    prefix: Box<[K]>,
}

impl<K: Eq + Clone, V> Trie<K, V> {
    /// constructs an empty prefix tree
    pub fn new() -> Self {
        Trie {
            root: TrieNode {
                value: None,
                prefix: Box::new([]),
                children: Vec::new(),
            },
        }
    }

    /// gets the value of a key
    #[inline]
    fn get(&self, key: &[K]) -> Option<&V> {
        self.root.get(key)
    }

    /// gets the value of a key as mutable
    #[inline]
    pub fn get_mut(&mut self, key: &[K]) -> Option<&mut V> {
        self.root.get_mut(key)
    }

    /// checks if a key exists
    #[inline]
    pub fn has(&self, key: &[K]) -> bool {
        self.get(key).is_some()
    }

    /// sets a key to a value
    /// returns the key evicted if there was already a key.
    #[inline]
    pub fn put(&mut self, key: &[K], val: V) -> Option<V> {
        self.root.insert(key, val)
    }

    /// sets a key to a value
    /// returns an Err() if the key already existed.
    #[inline]
    pub fn try_put(&mut self, key: &[K], val: V) -> Result<(), KeyExistsError> {
        match self.has(key) {
            true => Err(KeyExistsError),
            false => {
                self.put(key, val);
                Ok(())
            }
        }
    }

    /// removes a key
    ///
    /// Ok() if key existed, Err() otherwise
    #[inline]
    pub fn remove(&mut self, key: &[K]) -> Result<V, KeyNotFoundError> {
        match self.root.remove(key) {
            None => Err(KeyNotFoundError),
            Some(data) => Ok(data),
        }
    }

    /// Gets the size of the tree in terms of nodes.
    #[inline]
    pub fn size(&self) -> usize {
        self.root.size()
    }
}

impl<V> Trie<u8, V> {
    /// Puts a value in with a certain string key.
    /// The old value is ejected if it exists.
    pub fn put_str(&mut self, key: &str, val: V) -> Option<V> {
        self.put(key.as_bytes(), val)
    }

    /// Puts a value in with a certain string key.
    /// Errors if there is already a value for the given string.
    pub fn try_put_str(&mut self, key: &str, val: V) -> Result<(), KeyExistsError> {
        self.try_put(key.as_bytes(), val)
    }

    /// Gets a reference to the value associated to the bytes of a given string key.
    pub fn get_str(&mut self, key: &str) -> Option<&V> {
        self.get(key.as_bytes())
    }

    /// Gets a mutable reference to the value associated to the bytes of a given string key.
    pub fn get_mut_str(&mut self, key: &str) -> Option<&mut V> {
        self.get_mut(key.as_bytes())
    }

    /// Checks if a given string key is associated to a value.
    pub fn has_str(&mut self, key: &str) -> bool {
        self.has(key.as_bytes())
    }

    /// Removes a given string key from the Trie.
    pub fn remove_str(&mut self, key: &str) -> Result<V, KeyNotFoundError> {
        self.remove(key.as_bytes())
    }
}

impl<K: Eq + Clone, V> TrieNode<K, V> {
    fn size(&self) -> usize {
        let mut size = 1;
        for other in self.children.iter() {
            size += other.size();
        }
        return size;
    }

    fn get(&self, key: &[K]) -> Option<&V> {
        if key == self.prefix.as_ref() {
            return self.value.as_ref();
        }
        let rest = &key[self.prefix.len()..];
        let leaf = self.leaf(rest);
        match leaf {
            None => None,
            Some(node) => node.get(rest),
        }
    }

    fn leaf(&self, key: &[K]) -> Option<&Self> {
        for node in self.children.iter() {
            if key.starts_with(node.prefix.as_ref()) {
                return Some(&node);
            }
        }
        None
    }

    fn get_mut(&mut self, key: &[K]) -> Option<&mut V> {
        if key == self.prefix.as_ref() {
            return self.value.as_mut();
        }
        let rest = &key[self.prefix.len()..];
        let leaf = self.leaf_mut(rest);
        match leaf {
            None => None,
            Some(node) => node.get_mut(rest),
        }
    }

    fn leaf_mut(&mut self, key: &[K]) -> Option<&mut Self> {
        for node in self.children.iter_mut() {
            if key.starts_with(&node.prefix) {
                return Some(node);
            }
        }
        None
    }

    fn insert(&mut self, key: &[K], value: V) -> Option<V> {
        if key == self.prefix.as_ref() {
            return self.value.replace(value);
        }
        let rest = &key[self.prefix.len()..];
        let leaf = self.leaf_mut(rest);
        // still longer than leaf, and leaf exists
        if leaf.is_some() {
            return leaf.unwrap().insert(rest, value);
        }
        // shorter than a valid leaf split target
        let split = self.insert_split_target(rest);
        if split.is_some() {
            let (idx, node) = split.unwrap();
            let inject = TrieNode {
                prefix: (&rest[(rest.len() - 1)..(node.prefix.len() - rest.len())])
                    .to_owned()
                    .into_boxed_slice(),
                children: Vec::new(),
                value: Some(value),
            };
            let moved = std::mem::replace(&mut self.children[idx], inject);
            self.children[idx].children.push(moved);
            return None;
        }
        // neither a leaf is our prefix, nor are we a leaf prefix, inject new leaf.
        let inject = TrieNode {
            prefix: rest.to_owned().into_boxed_slice(),
            children: Vec::new(),
            value: Some(value),
        };
        self.children.push(inject);
        return None;
    }

    fn insert_split_target(&mut self, key: &[K]) -> Option<(usize, &mut Self)> {
        self.children
            .iter_mut()
            .enumerate()
            .find(|(_idx, node)| node.prefix.starts_with(key))
    }

    fn remove(&mut self, key: &[K]) -> Option<V> {
        if key == self.prefix.as_ref() {
            // us, this should only happen on first node. eject value.
            return self.value.take();
        }
        self.remove_internal(&key[self.prefix.len()..])
    }

    fn remove_internal(&mut self, key: &[K]) -> Option<V> {
        // get leaf node
        let rest = &key[self.prefix.len()..];
        let leaf = self.leaf_mut(rest);
        if leaf.is_none() {
            // not found, bail
            return None;
        }
        // unwrap it - this relies on local variable shadowing
        let leaf = leaf.unwrap();
        // leaf is not exact
        if leaf.prefix.as_ref() != rest {
            // kick it down
            return leaf.remove_internal(rest);
        }
        // leaf is exact
        // evict value
        let evicted = leaf.value.take();
        // some options
        match leaf.children.len() {
            0 => {
                // empty, evict
                let prefix = leaf.prefix.clone();
                self.evict_node_with_prefix(prefix.as_ref());
            }
            1 => {
                // 1 node. it should take the node below it.
                leaf.take_below();
            }
            _ => {
                // more than 1 node; do nothing, as it needs to stay there to be a split/branching node.
            }
        }
        match self.children.len() {
            1 => {
                // we only have one child, we should take the node we just read
                self.take_below();
            }
            _ => {
                // can't do anything, we need to be a branching node
            }
        }
        // return evicted value
        evicted
    }

    fn evict_node_with_prefix(&mut self, prefix: &[K]) {
        self.children.swap_remove(
            self.children
                .iter()
                .enumerate()
                .find(|(_idx, n)| n.prefix.as_ref() == prefix)
                .unwrap()
                .0,
        );
    }

    fn take_below(&mut self) {
        // this only makes sense if we only have 1 node.
        assert!(self.children.len() == 1);
        // take the node from below
        let taken = std::mem::replace(&mut self.children[0].children, Vec::new());
        // remove the node we have
        let node = self.children.remove(0);
        // steal their prefix
        let prefix = node.prefix.to_owned();
        // drop that node just in case
        std::mem::drop(node);
        // replace our children with that node
        self.children = taken;
        // append their prefix to ours
        self.prefix = [self.prefix.as_ref(), prefix.as_ref()].concat().into();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn insertion_retrieval() {
        let mut trie = Trie::new();
        let v1 = vec!["a", "ab", "ac", "b", "c", "abc", "abcde", "abced"];
        let v2 = vec![1, 2, 3, 4, 5, 6, 7, 9];
        for i in 0..8 {
            trie.put_str(v1[i], v2[i]);
        }
        for i in 0..8 {
            assert_eq!(trie.get_str(v1[i]), Some(&v2[i]));
        }
        assert_eq!(trie.size(), 9);
        trie.put_str(v1[3], 33);
        assert_eq!(trie.get_str(v1[3]), Some(&33));
        assert_eq!(trie.size(), 9);
    }

    #[test]
    fn insertion_deletion() {
        let mut trie = Trie::new();
        let v1 = vec!["a", "ab", "ac", "b", "c", "abc", "abcde", "abced"];
        let v2 = vec![1, 2, 3, 4, 5, 6, 7, 9];
        for i in 0..8 {
            trie.put_str(v1[i], v2[i]);
        }
        for i in 0..8 {
            assert_eq!(trie.get_str(v1[i]), Some(&v2[i]));
        }
        assert_eq!(trie.size(), 9);
        let removed = trie.remove_str("abcd");
        assert!(removed.is_err());
        let removed = trie.remove_str("abcde");
        assert_eq!(removed.ok(), Some(7));
        assert_eq!(trie.size(), 7);
        let removed: Result<i32, KeyNotFoundError> = trie.remove_str("c");
        assert_eq!(removed.ok(), Some(5));
        assert_eq!(trie.size(), 6);
        let removed = trie.remove_str("abcde");
        assert!(removed.is_err());
        assert_eq!(trie.size(), 6);
    }
}
