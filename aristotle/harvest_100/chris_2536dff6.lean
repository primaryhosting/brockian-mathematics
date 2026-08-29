/-
# Mobius Root Sum 10
Category: Pure Mathematics
Target: Math.mobius_root_sum_10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Mobius Root Sum 10
Category: Pure Mathematics
Target: Math.mobius_root_sum_10
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

set_option grind.warning false

namespace Math

/-- A fixed primitive 10-th root of unity in `ℂ`. -/
noncomputable def zeta10 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 10)

theorem isPrimitiveRoot_zeta10 : IsPrimitiveRoot zeta10 10 :=
  Complex.isPrimitiveRoot_exp 10 (by norm_num)

/-- The set of primitive 10-th roots of unity, explicitly. -/
theorem primitiveRoots_ten :
    primitiveRoots 10 ℂ = {zeta10, zeta10 ^ 3, zeta10 ^ 7, zeta10 ^ 9} := by
  have hz := isPrimitiveRoot_zeta10
  ext x
  rw [mem_primitiveRoots (by norm_num)]
  constructor
  · intro hx
    obtain ⟨i, hi, rfl⟩ := hz.eq_pow_of_pow_eq_one hx.pow_eq_one
    have hcop : Nat.Coprime i 10 := (hz.pow_iff_coprime (by norm_num) i).mp hx
    interval_cases i <;> simp_all [Nat.Coprime]
  · intro hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact hz
    · exact hz.pow_of_coprime 3 (by decide)
    · exact hz.pow_of_coprime 7 (by decide)
    · exact hz.pow_of_coprime 9 (by decide)

theorem zeta10_pow_five : zeta10 ^ 5 = -1 := by
  have hz := isPrimitiveRoot_zeta10
  have h10 : zeta10 ^ 10 = 1 := hz.pow_eq_one
  have h5 : zeta10 ^ 5 ≠ 1 := hz.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have hmul : (zeta10 ^ 5 - 1) * (zeta10 ^ 5 + 1) = 0 := by linear_combination h10
  rcases mul_eq_zero.mp hmul with h | h
  · exact absurd (sub_eq_zero.mp h) h5
  · linear_combination h

theorem zeta10_geom : 1 + zeta10 ^ 2 + zeta10 ^ 4 + zeta10 ^ 6 + zeta10 ^ 8 = 0 := by
  have hz := isPrimitiveRoot_zeta10
  have h10 : zeta10 ^ 10 = 1 := hz.pow_eq_one
  have h2 : zeta10 ^ 2 ≠ 1 := hz.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have hne : zeta10 ^ 2 - 1 ≠ 0 := sub_ne_zero.mpr h2
  have hmul : (zeta10 ^ 2 - 1) * (1 + zeta10 ^ 2 + zeta10 ^ 4 + zeta10 ^ 6 + zeta10 ^ 8) = 0 := by
    linear_combination h10
  exact (mul_eq_zero.mp hmul).resolve_left hne

/-- The sum of the primitive 10-th roots of unity equals `μ(10) = 1`. -/
theorem mobius_root_sum_10 :
    ∑ z ∈ primitiveRoots 10 ℂ, z = ((ArithmeticFunction.moebius 10 : ℤ) : ℂ) := by
  have hz := isPrimitiveRoot_zeta10
  have hne : ∀ i j : ℕ, i < 10 → j < 10 → i ≠ j → zeta10 ^ i ≠ zeta10 ^ j := by
    intro i j hi hj hij h
    exact hij (hz.pow_inj hi hj h)
  have h1 : zeta10 ^ 1 = zeta10 := pow_one _
  rw [primitiveRoots_ten]
  rw [Finset.sum_insert (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      push_neg
      refine ⟨?_, ?_, ?_⟩
      · simpa [h1] using hne 1 3 (by norm_num) (by norm_num) (by norm_num)
      · simpa [h1] using hne 1 7 (by norm_num) (by norm_num) (by norm_num)
      · simpa [h1] using hne 1 9 (by norm_num) (by norm_num) (by norm_num)),
    Finset.sum_insert (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      push_neg
      exact ⟨hne 3 7 (by norm_num) (by norm_num) (by norm_num),
        hne 3 9 (by norm_num) (by norm_num) (by norm_num)⟩),
    Finset.sum_insert (by
      simp only [Finset.mem_singleton]
      exact hne 7 9 (by norm_num) (by norm_num) (by norm_num)),
    Finset.sum_singleton]
  have hmu : (ArithmeticFunction.moebius 10 : ℤ) = 1 := by
    have h : (10 : ℕ) = 2 * 5 := by norm_num
    rw [h, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
      ArithmeticFunction.moebius_apply_prime (by norm_num),
      ArithmeticFunction.moebius_apply_prime (by norm_num)]
    norm_num
  rw [hmu]
  push_cast
  linear_combination (zeta10 + zeta10 ^ 2 + zeta10 ^ 3 + zeta10 ^ 4) * zeta10_pow_five
    - zeta10_geom

end Math

