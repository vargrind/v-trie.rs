use std::fmt::Debug;

use crate::{Trie, TrieNode};

type StackEntry<'a, K, V> = (&'a TrieNode<K, V>, Box<[K]>);

/// Iterator for the trie
/// The order of the returned key-value-pairs depends on the order of insertion
#[derive(Debug)]
pub struct TrieIterator<'a, K: Eq + Clone, V> {
    stack: Vec<StackEntry<'a, K, V>>,
}

impl<'a, K: Eq + Clone, V> TrieIterator<'a, K, V> {
    /// Create a new iterator for the given trie
    pub fn new(trie: &'a Trie<K, V>) -> Self {
        TrieIterator {
            stack: vec![(&trie.root, vec![].into_boxed_slice())],
        }
    }
}

impl<'a, K: Eq + Clone, V> Iterator for TrieIterator<'a, K, V> {
    type Item = (Box<[K]>, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        let mut result = None;
        while let Some((node, prefix)) = self.stack.pop() {
            if node.value.is_some() {
                result = Some((prefix.clone(), node.value.as_ref().unwrap()));
            }
            node.children.iter().for_each(|c| {
                let child_prefix: Vec<K> = prefix
                    .iter()
                    .cloned()
                    .chain(c.prefix.iter().cloned())
                    .collect();
                let child_prefix = child_prefix.into_boxed_slice();
                self.stack.push((c, child_prefix));
            });
            if result.is_some() {
                break;
            }
        }
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_trie_iterator_empty() {
        let trie: Trie<u8, u8> = Trie::new();
        let mut iter = TrieIterator::new(&trie);
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_trie_iterator_single_value() {
        let mut trie: Trie<u8, u8> = Trie::new();
        trie.insert(&[1, 2, 3], 42);
        let mut iter = TrieIterator::new(&trie);
        assert_eq!(
            iter.next(),
            Some((vec![1u8, 2u8, 3u8].into_boxed_slice(), &42u8))
        );
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_trie_iterator_multiple_values_linear_trie() {
        let mut trie: Trie<u8, u8> = Trie::new();
        trie.insert(&[1], 1);
        trie.insert(&[1, 2, 3], 123);
        let mut iter = TrieIterator::new(&trie);
        assert_eq!(iter.next(), Some((vec![1].into_boxed_slice(), &1)));
        assert_eq!(iter.next(), Some((vec![1, 2, 3].into_boxed_slice(), &123)));
    }

    #[test]
    fn test_trie_iterator_multiple_values_complex_trie() {
        let mut trie: Trie<u8, u16> = Trie::new();
        trie.insert(&[1], 1);
        trie.insert(&[1, 2, 3], 123);
        trie.insert(&[1, 2, 3, 4], 1234);
        trie.insert(&[1, 5, 6], 156);
        trie.insert(&[1, 5, 7], 157);
        trie.insert(&[8, 9], 89);
        let mut iter = TrieIterator::new(&trie);
        assert_eq!(iter.next(), Some((vec![8, 9].into_boxed_slice(), &89)));
        assert_eq!(iter.next(), Some((vec![1].into_boxed_slice(), &1)));
        assert_eq!(iter.next(), Some((vec![1, 5, 7].into_boxed_slice(), &157)));
        assert_eq!(iter.next(), Some((vec![1, 5, 6].into_boxed_slice(), &156)));
        assert_eq!(iter.next(), Some((vec![1, 2, 3].into_boxed_slice(), &123)));
        assert_eq!(
            iter.next(),
            Some((vec![1, 2, 3, 4].into_boxed_slice(), &1234))
        );
    }
}
