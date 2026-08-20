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

lemma bonferroni_choose (m k : ℕ) (hk : Even k) :
    (if m = 0 then (1 : ℝ) else 0) ≤ ∑ j ∈ range (k + 1), (-1 : ℝ) ^ j * (m.choose j : ℝ) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [if_pos rfl]
    rw [Finset.sum_eq_single 0]
    · simp
    · intro j _ hj
      simp [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hj)]
    · intro h; simp at h
  · rw [if_neg (by omega), alt_choose_sum m k hm, hk.neg_one_pow]
    positivity

/-- Set-theoretic Bonferroni inequality: the indicator that no `p ∈ P` satisfies `Q` is at most
the truncated (at even level `k`) inclusion-exclusion sum. -/
