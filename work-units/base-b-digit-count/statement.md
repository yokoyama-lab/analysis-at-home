# Base-b digit count: n < b^k => at most k digits

## Claim
> `2 <= b -> n < b ^ k -> ndigits fuel b n <= k`.

Generalizes `binary-search-comparisons` (b=2) to any base b >= 2; the minimal k with n < b^k is floor(log_b n)+1.

## Cost model
Reference Rocq proof (`digit_count_bound`, axiom-free): [`targets/rocq/DigitCount.v`](targets/rocq/DigitCount.v).
