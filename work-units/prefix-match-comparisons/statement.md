# Pattern match at a position uses at most |pattern| comparisons

## Claim
> `snd (pmatch p t) <= length p`.

## Cost model
Reference Rocq proof (`prefix_match_comparisons`, axiom-free): [`targets/rocq/PrefixMatch.v`](targets/rocq/PrefixMatch.v).
