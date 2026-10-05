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

/-
General linear algebra helpers: quotients `b / a` of nested submodules and additivity
of their dimensions along chains.
-/
import Mathlib

set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Math2

open Submodule

variable {k M N : Type*} [Field k] [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]

/-- The quotient `b / a` of two submodules (interesting when `a ≤ b`). -/
abbrev Qt (a b : Submodule k M) : Type _ := b ⧸ a.submoduleOf b

/-- `b / ⊥ ≃ b`. -/

lemma map_Lspace (D : Divisor Place) {x : K} (hx : x ≠ 0) :
    (V.Lspace D).map ((mulEquiv (k := k) hx : K ≃ₗ[k] K) : K →ₗ[k] K)
      = V.Lspace (D - V.divisorOf x) := by
  apply le_antisymm
  · rintro z ⟨y, hy, rfl⟩
    have hy' : y ∈ V.Lspace D := hy
    rw [mem_Lspace] at hy'
    rw [mem_Lspace]
    intro P
    show ((-((D - V.divisorOf x) P) : ℤ) : WithTop ℤ) ≤ V.ord P (x * y)
    rw [V.ord_mul, V.ord_of_ne P hx]
    have hP := hy' P
    calc ((-((D - V.divisorOf x) P) : ℤ) : WithTop ℤ)
        = ((V.v P x : ℤ) : WithTop ℤ) + ((-(D P) : ℤ) : WithTop ℤ) := by
          rw [← WithTop.coe_add]
          congr 1
          simp only [Finsupp.coe_sub, Pi.sub_apply]
          rw [V.divisorOf_apply hx]
          ring
      _ ≤ ((V.v P x : ℤ) : WithTop ℤ) + V.ord P y := add_le_add le_rfl hP
  · intro z hz
    rw [mem_Lspace] at hz
    refine ⟨x⁻¹ * z, ?_, ?_⟩
    · show x⁻¹ * z ∈ V.Lspace D
      rw [mem_Lspace]
      intro P
      have hP := hz P
      show ((-(D P) : ℤ) : WithTop ℤ) ≤ V.ord P (x⁻¹ * z)
      rw [V.ord_mul, V.ord_inv P hx]
      calc ((-(D P) : ℤ) : WithTop ℤ)
          = ((-(V.v P x) : ℤ) : WithTop ℤ) + ((-((D - V.divisorOf x) P) : ℤ) : WithTop ℤ) := by
            rw [← WithTop.coe_add]
            congr 1
            simp only [Finsupp.coe_sub, Pi.sub_apply]
            rw [V.divisorOf_apply hx]
            ring
        _ ≤ ((-(V.v P x) : ℤ) : WithTop ℤ) + V.ord P z := add_le_add le_rfl hP
    · show x * (x⁻¹ * z) = z
      field_simp

