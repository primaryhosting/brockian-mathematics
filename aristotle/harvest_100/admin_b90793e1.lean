import Mathlib

/-!
# Value At Ten
Category: Riemann Program
Target: Riemann.Mertens.value_at_ten
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open ArithmeticFunction

namespace Riemann.Mertens

/-- The Mertens function `M n = ∑_{k=1}^{n} μ k`. -/
def mertens (n : ℕ) : ℤ := ∑ k ∈ Finset.Icc 1 n, moebius k

private lemma mu_two : moebius 2 = -1 := moebius_apply_prime (by norm_num)

private lemma mu_three : moebius 3 = -1 := moebius_apply_prime (by norm_num)

private lemma mu_five : moebius 5 = -1 := moebius_apply_prime (by norm_num)

private lemma mu_seven : moebius 7 = -1 := moebius_apply_prime (by norm_num)

private lemma mu_four : moebius 4 = 0 := by
  refine moebius_eq_zero_of_not_squarefree fun h => ?_
  have := h 2 (by norm_num)
  simp at this

private lemma mu_eight : moebius 8 = 0 := by
  refine moebius_eq_zero_of_not_squarefree fun h => ?_
  have := h 2 (by norm_num)
  simp at this

private lemma mu_nine : moebius 9 = 0 := by
  refine moebius_eq_zero_of_not_squarefree fun h => ?_
  have := h 3 (by norm_num)
  simp at this

private lemma mu_six : moebius 6 = 1 := by
  rw [show (6 : ℕ) = 2 * 3 by norm_num,
    isMultiplicative_moebius.map_mul_of_coprime (by norm_num), mu_two, mu_three]
  norm_num

private lemma mu_ten : moebius 10 = 1 := by
  rw [show (10 : ℕ) = 2 * 5 by norm_num,
    isMultiplicative_moebius.map_mul_of_coprime (by norm_num), mu_two, mu_five]
  norm_num

/-- The Mertens function at `10`: `M(10) = ∑_{k=1}^{10} μ k = -1`. -/
theorem value_at_ten : ∑ k ∈ Finset.Icc 1 10, moebius k = -1 := by
  have expand : ∑ k ∈ Finset.Icc 1 10, moebius k
      = moebius 1 + moebius 2 + moebius 3 + moebius 4 + moebius 5 + moebius 6 + moebius 7
        + moebius 8 + moebius 9 + moebius 10 := by
    simp [Finset.sum_Icc_succ_top]
  rw [expand, moebius_apply_one, mu_two, mu_three, mu_four, mu_five, mu_six, mu_seven,
    mu_eight, mu_nine, mu_ten]
  norm_num

/-- The Mertens function at `10` equals `-1`. -/
theorem mertens_ten : mertens 10 = -1 := value_at_ten

end Riemann.Mertens

#print axioms Riemann.Mertens.value_at_ten

import Mathlib

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

