import Mathlib

/-!
# Master Theorem Case 1
Category: Computer Science
Target: CS.master_theorem_case1
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

open Finset

/-- For `b > 0`, taking the `k`-th (natural) power commutes with the real power `c`. -/

lemma geom_sum_le_inv_one_sub {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    ∑ j ∈ Finset.range n, q ^ j ≤ (1 - q)⁻¹ := by
  have h1 : (0:ℝ) < 1 - q := by linarith
  rw [geom_sum_eq (by linarith : q ≠ 1)]
  rw [div_le_iff_of_neg (by linarith : q - 1 < 0)]
  have : (0:ℝ) ≤ q ^ n := pow_nonneg hq0 n
  have h2 : (1 - q)⁻¹ * (q - 1) = -1 := by
    field_simp
    ring
  rw [h2]
  linarith

/-- **Master theorem, Case 1.**

Let `T` satisfy the divide-and-conquer recurrence `T(b^(k+1)) = a * T(b^k) + f(b^(k+1))`
(here `T k` and `f k` denote the values at `n = b^k`), with `a > 0`, `b > 1`, and
`f(n) = O(n^(log_b a - ε))` for some `ε > 0`.  Then `T(n) = Θ(n^(log_b a))`. -/
