/-
# Mobius Root Sum 11
Category: Pure Mathematics
Target: Math.mobius_root_sum_11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring `/-! ... -/`, so the
-- header above is a plain block comment and is repeated as a docstring below.)

import Mathlib

/-!
# Mobius Root Sum 11
Category: Pure Mathematics
Target: Math.mobius_root_sum_11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Math

/-- With `ζ = exp(2πi/11)`, the primitive 11-th roots of unity are exactly the
powers `ζ ^ k` for `1 ≤ k ≤ 10`. -/
theorem primitiveRoots_eleven_eq_image :
    primitiveRoots 11 ℂ =
      (Finset.Ico 1 11).image (fun k : ℕ => Complex.exp (2 * Real.pi * Complex.I / 11) ^ k) := by
  have h : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / 11)) 11 := by
    simpa using Complex.isPrimitiveRoot_exp 11 (by norm_num)
  ext z
  simp only [Finset.mem_image, Finset.mem_Ico]
  rw [mem_primitiveRoots (by norm_num)]
  constructor
  · intro hz
    obtain ⟨i, hi, rfl⟩ := h.eq_pow_of_pow_eq_one hz.pow_eq_one
    refine ⟨i, ⟨?_, hi⟩, rfl⟩
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · simp only [pow_zero] at hz
      have h11 : (11 : ℕ) = 1 :=
        hz.unique (IsPrimitiveRoot.one_right_iff.mpr rfl)
      exact absurd h11 (by norm_num)
    · exact hpos
  · rintro ⟨k, ⟨hk1, hk2⟩, rfl⟩
    refine h.pow_of_coprime k ?_
    have hp : Nat.Prime 11 := by norm_num
    refine (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr ?_))
    intro hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega

/-- The sum of the primitive 11-th roots of unity in `ℂ` equals `μ(11) = -1`. -/
theorem mobius_root_sum_11 :
    ∑ z ∈ primitiveRoots 11 ℂ, z = (ArithmeticFunction.moebius 11 : ℂ) := by
  have h : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / 11)) 11 := by
    simpa using Complex.isPrimitiveRoot_exp 11 (by norm_num)
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 11) with hζ
  have hgeom : ∑ i ∈ Finset.range 11, ζ ^ i = 0 := h.geom_sum_eq_zero (by norm_num)
  have hsplit : ∑ i ∈ Finset.range 11, ζ ^ i = 1 + ∑ i ∈ Finset.Ico 1 11, ζ ^ i := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by norm_num)]
    norm_num
  have hIco : ∑ i ∈ Finset.Ico 1 11, ζ ^ i = -1 := by
    have := hsplit.symm.trans hgeom
    linear_combination this
  have hinj : Set.InjOn (fun k : ℕ => ζ ^ k) (Finset.Ico 1 11) := by
    intro a ha b hb hab
    simp only [Finset.coe_Ico, Set.mem_Ico] at ha hb
    exact h.pow_inj (by omega) (by omega) hab
  rw [primitiveRoots_eleven_eq_image, Finset.sum_image (fun a ha b hb hab => hinj ha hb hab), hIco]
  have : ArithmeticFunction.moebius 11 = -1 :=
    ArithmeticFunction.moebius_apply_prime (by norm_num)
  rw [this]
  norm_num

end Math

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

