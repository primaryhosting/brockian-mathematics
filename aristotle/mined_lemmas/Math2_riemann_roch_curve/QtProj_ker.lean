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

lemma QtProj_ker {a b c : Submodule k M} (hab : a ≤ b) (hbc : b ≤ c) :
    LinearMap.ker (QtProj (c := c) hab) = LinearMap.range (QtIncl hab hbc) := by
  apply le_antisymm
  · rw [SetLike.le_def]
    intro y
    refine Submodule.Quotient.induction_on _ y ?_
    intro x hx
    have hx' : x ∈ b.submoduleOf c := by
      rw [LinearMap.mem_ker] at hx
      rwa [show (QtProj (c := c) hab) (Submodule.Quotient.mk x) = Submodule.Quotient.mk x from rfl,
        Submodule.Quotient.mk_eq_zero] at hx
    have hxb : (x : M) ∈ b := hx'
    exact ⟨Submodule.Quotient.mk ⟨(x : M), hxb⟩, rfl⟩
  · rintro y ⟨z, rfl⟩
    refine Submodule.Quotient.induction_on _ z ?_
    intro w
    rw [LinearMap.mem_ker, QtIncl_apply,
      show (QtProj (c := c) hab) (Submodule.Quotient.mk (Submodule.inclusion hbc w))
        = Submodule.Quotient.mk (Submodule.inclusion hbc w) from rfl,
      Submodule.Quotient.mk_eq_zero]
    exact w.2

/-- Rank additivity along a chain `a ≤ b ≤ c`. -/
