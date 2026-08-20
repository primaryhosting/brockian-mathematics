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

namespace QC

open Complex

/-- The primitive 8-th root of unity raised to an integer power `d`,
written as `exp (2 π i d / 8)`. -/

lemma zeta8_eq_one_iff (d : ℤ) : zeta8 d = 1 ↔ (8 : ℤ) ∣ d := by
  rw [zeta8, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hpi : (Real.pi : ℂ) ≠ 0 := by
      exact_mod_cast Real.pi_ne_zero
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    have h : (d : ℂ) = ((8 * n : ℤ) : ℂ) := by
      push_cast
      field_simp at hn
      linear_combination hn
    exact_mod_cast h
  · rintro ⟨m, rfl⟩
    exact ⟨m, by push_cast; ring⟩

