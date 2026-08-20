import RequestProject.Mertens

/-!
# The main term: `∏_{3 ≤ p ≤ z} (1 - 2/p) ≤ 16 / (log z)^2`

This is proved by the elementary Euler-type argument: expanding `∏ (1 + 1/(p-1))` over
subsets dominates `∑_{a ≤ z squarefree} 1/a`, which in turn is at least half the harmonic
sum, hence at least `(log z)/2`.
-/

namespace Brun

open Finset


lemma sum_inv_le_two_sqrt (J : ℕ) : ∑ i ∈ Icc 1 J, (1 / i : ℝ) ≤ 2 * Real.sqrt J := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have ha : Real.sqrt J ^ 2 = J := Real.sq_sqrt (by positivity)
    have hb : Real.sqrt (J + 1) ^ 2 = (J : ℝ) + 1 := Real.sq_sqrt (by positivity)
    have hab : Real.sqrt J ≤ Real.sqrt (J + 1) :=
      Real.sqrt_le_sqrt (by linarith)
    have hb1 : 1 ≤ Real.sqrt (J + 1) := by
      have h1 : Real.sqrt 1 ≤ Real.sqrt ((J : ℝ) + 1) :=
        Real.sqrt_le_sqrt (by linarith [(Nat.cast_nonneg J : (0:ℝ) ≤ J)])
      simpa using h1
    have key : 1 / ((J : ℝ) + 1) ≤ 2 * Real.sqrt (J + 1) - 2 * Real.sqrt J := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [Real.sqrt_nonneg (J:ℝ), Real.sqrt_nonneg ((J:ℝ)+1)]
    push_cast
    push_cast at ih
    linarith

/-- The Mertens-type bound we need: the sum of `2/p` over odd primes `p ≤ 2^J`. -/
