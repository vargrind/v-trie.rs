# `v-trie`

A generic compressed prefix tree implementation in Rust.

This works on any sliceable sequence where the sequence can by copied; e.g. string, vectors of numbers, etc.

Performance directly depends on iteration and comparison through said slice.

