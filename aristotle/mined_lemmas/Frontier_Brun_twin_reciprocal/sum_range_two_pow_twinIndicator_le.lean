import Mathlib
import RequestProject.Brun.Final

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-- **Brun's theorem**: the sum of the reciprocals of the twin primes converges.

The twin primes are indexed by the subtype of naturals `p` such that both `p` and `p + 2`
are prime, and the summand is `1 / p`. -/

lemma sum_range_two_pow_twinIndicator_le (M : ℕ) :
    ∑ n ∈ range (2 ^ M), twinIndicator n
      ≤ ∑ m ∈ range M, (twinCount (2 ^ (m + 1)) : ℝ) / 2 ^ m := by
  induction M with
  | zero => simp [twinIndicator]
  | succ M ih =>
      have hsplit : ∑ n ∈ range (2 ^ (M + 1)), twinIndicator n
          = ∑ n ∈ range (2 ^ M), twinIndicator n
            + ∑ n ∈ Ico (2 ^ M) (2 ^ (M + 1)), twinIndicator n := by
        rw [Finset.range_eq_Ico,
          ← Finset.sum_Ico_consecutive _ (Nat.zero_le (2 ^ M))
            (Nat.pow_le_pow_right (by norm_num) (by omega) : 2 ^ M ≤ 2 ^ (M + 1))]
      rw [hsplit, Finset.sum_range_succ]
      have := sum_Ico_twinIndicator_le M
      linarith

/-- Summability of the twin prime indicator series, given the dyadic bound. -/
