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

noncomputable def QtCongr {a b a' b' : Submodule k M} (hab : a ≤ b) (e : M ≃ₗ[k] M)
    (ha : a.map (e : M →ₗ[k] M) = a') (hb : b.map (e : M →ₗ[k] M) = b') :
    Qt a b ≃ₗ[k] Qt a' b' := by
  set E : b ≃ₗ[k] b' := (e.submoduleMap b).trans (LinearEquiv.ofEq _ _ hb) with hE
  have hEc : ∀ x : b, ((E x : b') : M) = e (x : M) := fun x => rfl
  refine Submodule.Quotient.equiv _ _ E ?_
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    show ((E x : b') : M) ∈ a'
    rw [hEc, ← ha]
    exact ⟨(x : M), hx, rfl⟩
  · intro y hy
    have hy' : ((y : b') : M) ∈ a' := hy
    rw [← ha] at hy'
    obtain ⟨z, hz, hze⟩ := hy'
    refine ⟨⟨z, hab hz⟩, hz, ?_⟩
    apply Subtype.ext
    exact hze

/-- The canonical injection `b / a → c / a` for `a ≤ b ≤ c`. -/
