/-
# Value At Ten
Category: Riemann Program
Target: Riemann.Mertens.value_at_ten
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Value At Ten
Category: Riemann Program
Target: Riemann.Mertens.value_at_ten
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Riemann.Mertens

open ArithmeticFunction

/-- The Mertens function `M n = ∑_{k=1}^{n} μ k`. -/
def mertens (n : ℕ) : ℤ := ∑ k ∈ Finset.Icc 1 n, moebius k

private lemma not_squarefree_nine : ¬ Squarefree 9 := by
  intro h
  have := h 3 (by norm_num)
  norm_num [Nat.isUnit_iff] at this

private lemma mu_three : moebius 3 = -1 := moebius_apply_prime Nat.prime_three

private lemma mu_five : moebius 5 = -1 :=
  moebius_apply_prime (by norm_num)

private lemma mu_seven : moebius 7 = -1 :=
  moebius_apply_prime (by norm_num)

private lemma mu_four : moebius 4 = 0 :=
  moebius_eq_zero_of_not_squarefree (by decide)

private lemma mu_eight : moebius 8 = 0 :=
  moebius_eq_zero_of_not_squarefree (by decide)

private lemma mu_nine : moebius 9 = 0 :=
  moebius_eq_zero_of_not_squarefree not_squarefree_nine

private lemma mu_six : moebius 6 = 1 := by
  have := isMultiplicative_moebius.map_mul_of_coprime (m := 2) (n := 3) (by norm_num)
  simpa [moebius_apply_prime Nat.prime_two, mu_three] using this

private lemma mu_ten : moebius 10 = 1 := by
  have := isMultiplicative_moebius.map_mul_of_coprime (m := 2) (n := 5) (by norm_num)
  simpa [moebius_apply_prime Nat.prime_two, mu_five] using this

/-- The Mertens function at `10` equals `-1`. -/
theorem value_at_ten : ∑ k ∈ Finset.Icc 1 10, moebius k = -1 := by
  simp only [Finset.sum_Icc_succ_top (by norm_num : (1:ℕ) ≤ 10),
    Finset.sum_Icc_succ_top (by norm_num : (1:ℕ) ≤ 9),
    Finset.sum_Icc_succ_top (by norm_num : (1:ℕ) ≤ 8),
    Finset.sum_Icc_succ_top (by norm_num : (1:ℕ) ≤ 7),
    Finset.sum_Icc_succ_top (by norm_num : (1:ℕ) ≤ 6),
    Finset.sum_Icc_succ_top (by norm_num : (1:ℕ) ≤ 5),
    Finset.sum_Icc_succ_top (by norm_num : (1:ℕ) ≤ 4),
    Finset.sum_Icc_succ_top (by norm_num : (1:ℕ) ≤ 3),
    Finset.sum_Icc_succ_top (by norm_num : (1:ℕ) ≤ 2),
    Finset.sum_Icc_succ_top (by norm_num : (1:ℕ) ≤ 1)]
  rw [moebius_apply_prime Nat.prime_two, mu_three, mu_four, mu_five, mu_six, mu_seven,
    mu_eight, mu_nine, mu_ten]
  simp

/-- `mertens 10 = -1`. -/
theorem mertens_ten : mertens 10 = -1 := value_at_ten

end Riemann.Mertens

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

