/-
# Value At Ten
Category: Riemann Program
Target: Riemann.Mertens.value_at_ten
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` commands to precede any module docstring `/-! ... -/`,
-- so the required header above appears as a plain block comment, and is repeated
-- as a module docstring immediately after the import.)

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
open scoped ArithmeticFunction.Moebius

/-- The Mertens function `M(n) = ∑_{k=1}^{n} μ(k)`, where `μ` is the Möbius function. -/
def mertens (n : ℕ) : ℤ := ∑ k ∈ Finset.Icc 1 n, μ k

section Values

private lemma moebius_two : μ 2 = -1 := moebius_apply_prime (by norm_num)

private lemma moebius_three : μ 3 = -1 := moebius_apply_prime (by norm_num)

private lemma moebius_four : μ 4 = 0 := by
  rw [show (4 : ℕ) = 2 ^ 2 from rfl, moebius_apply_prime_pow (by norm_num) (by norm_num)]
  norm_num

private lemma moebius_five : μ 5 = -1 := moebius_apply_prime (by norm_num)

private lemma moebius_six : μ 6 = 1 := by
  rw [show (6 : ℕ) = 2 * 3 from rfl,
    isMultiplicative_moebius.map_mul_of_coprime (by norm_num), moebius_two, moebius_three]
  norm_num

private lemma moebius_seven : μ 7 = -1 := moebius_apply_prime (by norm_num)

private lemma moebius_eight : μ 8 = 0 := by
  rw [show (8 : ℕ) = 2 ^ 3 from rfl, moebius_apply_prime_pow (by norm_num) (by norm_num)]
  norm_num

private lemma moebius_nine : μ 9 = 0 := by
  rw [show (9 : ℕ) = 3 ^ 2 from rfl, moebius_apply_prime_pow (by norm_num) (by norm_num)]
  norm_num

private lemma moebius_ten : μ 10 = 1 := by
  rw [show (10 : ℕ) = 2 * 5 from rfl,
    isMultiplicative_moebius.map_mul_of_coprime (by norm_num), moebius_two, moebius_five]
  norm_num

end Values

/-- The Mertens function at `10`: `M(10) = ∑_{k=1}^{10} μ(k) = -1`. -/
theorem value_at_ten : mertens 10 = -1 := by
  have hsum : mertens 10 =
      μ 1 + μ 2 + μ 3 + μ 4 + μ 5 + μ 6 + μ 7 + μ 8 + μ 9 + μ 10 := by
    simp [mertens, Finset.sum_Icc_succ_top]
  rw [hsum, moebius_apply_one, moebius_two, moebius_three, moebius_four, moebius_five,
    moebius_six, moebius_seven, moebius_eight, moebius_nine, moebius_ten]
  norm_num

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

