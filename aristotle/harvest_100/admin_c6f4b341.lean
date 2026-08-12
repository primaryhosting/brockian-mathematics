/-
# Value At Ten
Category: Riemann Program
Target: Riemann.Mertens.value_at_ten
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open ArithmeticFunction

namespace Riemann.Mertens

/-- The Mertens function `M n = ∑_{k=1}^{n} μ k`, where `μ` is the Möbius function. -/
def mertens (n : ℕ) : ℤ := ∑ k ∈ Finset.Icc 1 n, moebius k

private lemma not_squarefree_four : ¬ Squarefree 4 := by
  intro h
  have := h 2 ⟨1, by norm_num⟩
  rw [Nat.isUnit_iff] at this
  omega

private lemma not_squarefree_eight : ¬ Squarefree 8 := by
  intro h
  have := h 2 ⟨2, by norm_num⟩
  rw [Nat.isUnit_iff] at this
  omega

private lemma not_squarefree_nine : ¬ Squarefree 9 := by
  intro h
  have := h 3 ⟨1, by norm_num⟩
  rw [Nat.isUnit_iff] at this
  omega

private lemma moebius_six : moebius 6 = 1 := by
  rw [show (6 : ℕ) = 2 * 3 by norm_num,
    isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    moebius_apply_prime Nat.prime_two, moebius_apply_prime Nat.prime_three]
  ring

private lemma moebius_ten : moebius 10 = 1 := by
  rw [show (10 : ℕ) = 2 * 5 by norm_num,
    isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    moebius_apply_prime Nat.prime_two, moebius_apply_prime (by norm_num)]
  ring

/-- The Mertens function at `10`: `M(10) = ∑_{k=1}^{10} μ k = -1`. -/
theorem value_at_ten : mertens 10 = -1 := by
  have h4 : moebius 4 = 0 := moebius_eq_zero_of_not_squarefree not_squarefree_four
  have h8 : moebius 8 = 0 := moebius_eq_zero_of_not_squarefree not_squarefree_eight
  have h9 : moebius 9 = 0 := moebius_eq_zero_of_not_squarefree not_squarefree_nine
  rw [mertens, show Finset.Icc 1 10 = ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10} : Finset ℕ) by decide]
  norm_num [Finset.sum_insert, Finset.mem_insert, h4, h8, h9, moebius_six, moebius_ten,
    moebius_apply_prime Nat.prime_two, moebius_apply_prime Nat.prime_three,
    moebius_apply_prime (show Nat.Prime 5 by norm_num),
    moebius_apply_prime (show Nat.Prime 7 by norm_num)]

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

