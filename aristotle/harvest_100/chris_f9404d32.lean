import Mathlib

/-!
# Value At Ten
Category: Riemann Program
Target: Riemann.Mertens.value_at_ten
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


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

namespace Riemann
namespace Mertens

/-- The Mertens function `M n = ∑_{k=1}^{n} μ k`, where `μ` is the Möbius function. -/
def M (n : ℕ) : ℤ := ∑ k ∈ Finset.Icc 1 n, ArithmeticFunction.moebius k

/-- Möbius value at a product of two coprime numbers. -/
private lemma moebius_mul_coprime {m n : ℕ} (h : Nat.Coprime m n) :
    ArithmeticFunction.moebius (m * n) =
      ArithmeticFunction.moebius m * ArithmeticFunction.moebius n :=
  ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime h

private lemma moebius_two : ArithmeticFunction.moebius 2 = -1 :=
  ArithmeticFunction.moebius_apply_prime Nat.prime_two

private lemma moebius_three : ArithmeticFunction.moebius 3 = -1 :=
  ArithmeticFunction.moebius_apply_prime Nat.prime_three

private lemma moebius_five : ArithmeticFunction.moebius 5 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private lemma moebius_seven : ArithmeticFunction.moebius 7 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private lemma moebius_four : ArithmeticFunction.moebius 4 = 0 :=
  ArithmeticFunction.moebius_eq_zero_of_not_squarefree (by decide)

private lemma moebius_eight : ArithmeticFunction.moebius 8 = 0 :=
  ArithmeticFunction.moebius_eq_zero_of_not_squarefree (by decide)

private lemma moebius_nine : ArithmeticFunction.moebius 9 = 0 := by
  refine ArithmeticFunction.moebius_eq_zero_of_not_squarefree (fun h => ?_)
  have h3 : IsUnit (3 : ℕ) := h 3 (by norm_num)
  rw [Nat.isUnit_iff] at h3
  exact absurd h3 (by norm_num)

private lemma moebius_six : ArithmeticFunction.moebius 6 = 1 := by
  have h : ArithmeticFunction.moebius (2 * 3) =
      ArithmeticFunction.moebius 2 * ArithmeticFunction.moebius 3 :=
    moebius_mul_coprime (by decide)
  norm_num [moebius_two, moebius_three] at h
  exact h

private lemma moebius_ten : ArithmeticFunction.moebius 10 = 1 := by
  have h : ArithmeticFunction.moebius (2 * 5) =
      ArithmeticFunction.moebius 2 * ArithmeticFunction.moebius 5 :=
    moebius_mul_coprime (by decide)
  norm_num [moebius_two, moebius_five] at h
  exact h

/-- The Mertens function at `10`: `M 10 = ∑_{k=1}^{10} μ k = -1`. -/
theorem value_at_ten : M 10 = -1 := by
  have hIcc : Finset.Icc 1 10 = ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10} : Finset ℕ) := by decide
  rw [M, hIcc]
  norm_num [Finset.sum_insert, ArithmeticFunction.moebius_apply_one, moebius_two, moebius_three,
    moebius_four, moebius_five, moebius_six, moebius_seven, moebius_eight, moebius_nine,
    moebius_ten]

end Mertens
end Riemann

