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

lemma finrank_Qt_Kge_succ (P : Place) (m : ℤ) :
    Module.finrank k (Qt (V.Kge P (m + 1)) (V.Kge P m)) = V.degP P := by
  obtain ⟨u, hu, hvu⟩ := V.exists_val_eq P m
  have e : Qt (V.Kge P 1) (V.Kge P 0) ≃ₗ[k] Qt (V.Kge P (m + 1)) (V.Kge P m) := by
    refine QtCongr (V.Kge_mono (by norm_num)) (mulEquiv (k := k) hu) ?_ ?_
    · rw [V.map_Kge P 1 hu, hvu, add_comm]
    · rw [V.map_Kge P 0 hu, hvu, zero_add]
  exact (e.finrank_eq).symm

omit hfin in
