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

/-- The Mertens function `M n = ∑_{k=1}^{n} μ k`. -/
def mertens (n : ℕ) : ℤ := ∑ k ∈ Finset.Icc 1 n, moebius k

private lemma moebius_two : moebius 2 = -1 :=
  ArithmeticFunction.moebius_apply_prime Nat.prime_two

private lemma moebius_three : moebius 3 = -1 :=
  ArithmeticFunction.moebius_apply_prime Nat.prime_three

private lemma moebius_five : moebius 5 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private lemma moebius_seven : moebius 7 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private lemma moebius_four : moebius 4 = 0 := by
  have h : (4 : ℕ) = 2 ^ 2 := by norm_num
  rw [h, ArithmeticFunction.moebius_apply_prime_pow Nat.prime_two (by norm_num)]
  norm_num

private lemma moebius_eight : moebius 8 = 0 := by
  have h : (8 : ℕ) = 2 ^ 3 := by norm_num
  rw [h, ArithmeticFunction.moebius_apply_prime_pow Nat.prime_two (by norm_num)]
  norm_num

private lemma moebius_nine : moebius 9 = 0 := by
  have h : (9 : ℕ) = 3 ^ 2 := by norm_num
  rw [h, ArithmeticFunction.moebius_apply_prime_pow Nat.prime_three (by norm_num)]
  norm_num

private lemma moebius_six : moebius 6 = 1 := by
  have h : (6 : ℕ) = 2 * 3 := by norm_num
  rw [h, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    moebius_two, moebius_three]
  norm_num

private lemma moebius_ten : moebius 10 = 1 := by
  have h : (10 : ℕ) = 2 * 5 := by norm_num
  rw [h, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    moebius_two, moebius_five]
  norm_num

/-- The Mertens function at `10`: `M(10) = ∑_{k=1}^{10} μ(k) = -1`. -/
theorem value_at_ten : ∑ k ∈ Finset.Icc 1 10, moebius k = -1 := by
  simp only [show Finset.Icc 1 10 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10} from rfl]
  norm_num [ArithmeticFunction.moebius_apply_one, moebius_two, moebius_three, moebius_four,
    moebius_five, moebius_six, moebius_seven, moebius_eight, moebius_nine, moebius_ten]

/-- Restatement in terms of the Mertens function: `M(10) = -1`. -/
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

