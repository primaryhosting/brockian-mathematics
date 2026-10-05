import Mathlib


def Hyperperfect (k n : ℕ) : Prop := 0 < n ∧ k * sigma1 n = (k + 1) * n + (k - 1)

/-- A `k`-hyperperfect number (for `k ≥ 1`) is either `1` or at least `3`;
the only case to rule out is `n = 2`, where `sigma1 2 = 3` gives `3k = 3k + 1`.
(The hypothesis `1 ≤ k` is part of the requested statement but is not needed.) -/
