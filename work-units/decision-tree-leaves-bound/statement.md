# Comparison-sort lower bound core

## Claim
> `leaves t <= 2 ^ height t`.

This is the heart of the Ω(n log n) comparison-sort lower bound (Vol 3 §5.3.1): any comparison sort is a binary **decision tree** whose leaves are the n! possible orderings. Since a tree of height h has at most 2^h leaves, distinguishing n! cases forces 2^h ≥ n!, i.e. the worst-case number of comparisons h ≥ ⌈lg n!⌉ = Ω(n log n).

## Cost model
Reference Rocq proof (`decision_tree_leaves_bound`, axiom-free): [`targets/rocq/DecisionTree.v`](targets/rocq/DecisionTree.v).
