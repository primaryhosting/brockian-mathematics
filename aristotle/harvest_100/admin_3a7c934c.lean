/-
# Mobius Root Sum 5
Category: Pure Mathematics
Target: Math.mobius_root_sum_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 1000000

namespace Math

/-- The primitive 5-th roots of unity in `ℂ` are exactly the powers `ζ, ζ², ζ³, ζ⁴`
of `ζ = exp(2πi/5)`. -/
lemma primitiveRoots_five_eq_image :
    primitiveRoots 5 ℂ =
      Finset.image (fun i : ℕ => Complex.exp (2 * Real.pi * Complex.I / 5) ^ i) {1, 2, 3, 4} := by
  have hz : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / 5)) 5 :=
    Complex.isPrimitiveRoot_exp 5 (by norm_num)
  ext x
  simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton,
    mem_primitiveRoots (show 0 < 5 by norm_num)]
  constructor
  · intro hx
    obtain ⟨i, hi, rfl⟩ := hz.eq_pow_of_pow_eq_one hx.pow_eq_one
    refine ⟨i, ?_, rfl⟩
    interval_cases i
    · exfalso
      simp only [pow_zero] at hx
      have := hx.unique (IsPrimitiveRoot.one_right_iff.mpr rfl)
      omega
    · tauto
    · tauto
    · tauto
    · tauto
  · rintro ⟨i, hi, rfl⟩
    refine hz.pow_of_coprime i ?_
    rcases hi with h | h | h | h <;> subst h <;> decide

/-- The sum of the primitive 5-th roots of unity equals `μ(5) = -1`. -/
theorem mobius_root_sum_5 :
    ∑ z ∈ primitiveRoots 5 ℂ, z = ((ArithmeticFunction.moebius 5 : ℤ) : ℂ) := by
  have hz : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / 5)) 5 :=
    Complex.isPrimitiveRoot_exp 5 (by norm_num)
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5) with hζdef
  have hinj : Set.InjOn (fun i : ℕ => ζ ^ i) ({1, 2, 3, 4} : Finset ℕ) := by
    intro a ha b hb hab
    have ha' : a < 5 := by
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
        Set.mem_singleton_iff] at ha
      rcases ha with h | h | h | h <;> omega
    have hb' : b < 5 := by
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
        Set.mem_singleton_iff] at hb
      rcases hb with h | h | h | h <;> omega
    exact hz.pow_inj ha' hb' hab
  have hsum : ∑ i ∈ Finset.range 5, ζ ^ i = 0 := hz.geom_sum_eq_zero (by norm_num)
  have hmu : (ArithmeticFunction.moebius 5 : ℤ) = -1 := by
    have h5 : Nat.Prime 5 := by norm_num
    simp [ArithmeticFunction.moebius_apply_prime h5]
  rw [primitiveRoots_five_eq_image, Finset.sum_image (by
    intro a ha b hb hab; exact hinj ha hb hab), hmu]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one, pow_zero] at hsum
  push_cast
  linear_combination hsum

end Math

