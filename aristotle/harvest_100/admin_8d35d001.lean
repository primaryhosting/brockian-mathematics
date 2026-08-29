/-
# Value At Ten
Category: Riemann Program
Target: Riemann.Mertens.value_at_ten
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Riemann.Mertens

open ArithmeticFunction

/-- The Mertens function `M n = ∑_{k=1}^{n} μ k`, where `μ` is the Möbius function. -/
def M (n : ℕ) : ℤ := ∑ k ∈ Finset.Icc 1 n, moebius k

lemma moebius_two : moebius 2 = -1 := moebius_apply_prime (by norm_num)

lemma moebius_three : moebius 3 = -1 := moebius_apply_prime (by norm_num)

lemma moebius_five : moebius 5 = -1 := moebius_apply_prime (by norm_num)

lemma moebius_seven : moebius 7 = -1 := moebius_apply_prime (by norm_num)

lemma moebius_four : moebius 4 = 0 := by
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num,
    moebius_apply_prime_pow (by norm_num) (by norm_num)]
  norm_num

lemma moebius_eight : moebius 8 = 0 := by
  rw [show (8 : ℕ) = 2 ^ 3 by norm_num,
    moebius_apply_prime_pow (by norm_num) (by norm_num)]
  norm_num

lemma moebius_nine : moebius 9 = 0 := by
  rw [show (9 : ℕ) = 3 ^ 2 by norm_num,
    moebius_apply_prime_pow (by norm_num) (by norm_num)]
  norm_num

lemma moebius_six : moebius 6 = 1 := by
  rw [show (6 : ℕ) = 2 * 3 by norm_num,
    isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    moebius_two, moebius_three]
  norm_num

lemma moebius_ten : moebius 10 = 1 := by
  rw [show (10 : ℕ) = 2 * 5 by norm_num,
    isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    moebius_two, moebius_five]
  norm_num

/-- The Mertens function at `10`: `M 10 = ∑_{k=1}^{10} μ k = -1`. -/
theorem value_at_ten : M 10 = -1 := by
  have hIcc : Finset.Icc 1 10 = ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10} : Finset ℕ) := by decide
  rw [M, hIcc]
  norm_num [moebius_two, moebius_three, moebius_four, moebius_five, moebius_six,
    moebius_seven, moebius_eight, moebius_nine, moebius_ten]

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

