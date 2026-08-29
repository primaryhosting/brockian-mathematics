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

lemma map_Kge (P : Place) (m : ℤ) {u : K} (hu : u ≠ 0) :
    (V.Kge P m).map ((mulEquiv (k := k) hu : K ≃ₗ[k] K) : K →ₗ[k] K)
      = V.Kge P (m + V.v P u) := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    simp only [mem_Kge] at hx ⊢
    show ((m + V.v P u : ℤ) : WithTop ℤ) ≤ V.ord P (u * x)
    rw [V.ord_mul, V.ord_of_ne P hu]
    push_cast
    rw [add_comm ((V.v P u : WithTop ℤ)) _]
    exact add_le_add hx le_rfl
  · intro y hy
    simp only [mem_Kge] at hy
    refine ⟨u⁻¹ * y, ?_, ?_⟩
    swap
    · show u * (u⁻¹ * y) = y
      field_simp
    show ((m : ℤ) : WithTop ℤ) ≤ V.ord P (u⁻¹ * y)
    rw [V.ord_mul, V.ord_inv P hu]
    calc ((m : ℤ) : WithTop ℤ)
        = ((-(V.v P u) : ℤ) : WithTop ℤ) + ((m + V.v P u : ℤ) : WithTop ℤ) := by
          rw [← WithTop.coe_add]
          congr 1
          ring
      _ ≤ ((-(V.v P u) : ℤ) : WithTop ℤ) + V.ord P y := add_le_add le_rfl hy

/-! ### The degree of a place -/

/-- The degree of the place `P`: the dimension of its residue field over `k`. -/
