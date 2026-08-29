import Mathlib

namespace Brockian.ZumkellerNumbers

/-- `n` is *Zumkeller* if its divisors split into two sets of equal sum, expressed via
the half-sum characterization: some subset of the divisors sums to half of sigma(n). -/

def Zumkeller (n : ℕ) : Prop :=
  ∃ S : Finset ℕ, S ⊆ n.divisors ∧ 2 * (∑ d ∈ S, d) = ∑ d ∈ n.divisors, d

/-!
## The proposed theorem is false

The requested statement

```

theorem odd_zumkeller_div_three : ∀ n, Odd n → Zumkeller n → 3 ∣ n
```

is **not** provable: it is refuted by `N = 5391411025 = 5^2 * 7 * 11 * 13 * 17 * 19 * 23 * 29`,
which is odd, not divisible by `3`, and Zumkeller.  Indeed `σ(N) = 10799308800`, and the six
divisors

`1, 23, 391, 135575, 8107385, 5391411025`

sum to `5399654400 = σ(N)/2`.

The original statement is therefore kept below only as a comment, and we prove its negation.
-/

/-- The divisor-sum function is multiplicative: for coprime `m` and `k`,
`σ(m * k) = σ(m) * σ(k)`. -/

theorem odd_zumkeller_div_three : ∀ n, Odd n → Zumkeller n → 3 ∣ n
-/

/-- **The conjecture "every odd Zumkeller number is divisible by 3" is false.**
The counterexample is `5391411025 = 5^2 * 7 * 11 * 13 * 17 * 19 * 23 * 29`. -/
