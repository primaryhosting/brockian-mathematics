import Mathlib

/-- The aliquot sum of `n`: the sum of the proper divisors of `n`. -/

theorem sigma_eq_aliquot_add_self {n : ℕ} (hn : 0 < n) :
    ∑ d ∈ n.divisors, d = aliquot n + n :=
  Nat.sum_divisors_eq_sum_properDivisors_add_self

