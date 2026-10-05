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

lemma finrank_Qt_add {a b c : Submodule k M} (hab : a ≤ b) (hbc : b ≤ c)
    [Module.Finite k (Qt a b)] [Module.Finite k (Qt b c)] :
    Module.finrank k (Qt a b) + Module.finrank k (Qt b c) = Module.finrank k (Qt a c) := by
  have h := rank_Qt_add hab hbc
  have e1 : Module.rank k (Qt a b) = (Module.finrank k (Qt a b) : Cardinal) :=
    (Module.finrank_eq_rank k _).symm
  have e2 : Module.rank k (Qt b c) = (Module.finrank k (Qt b c) : Cardinal) :=
    (Module.finrank_eq_rank k _).symm
  rw [e1, e2] at h
  have hc : Module.rank k (Qt a c) = ((Module.finrank k (Qt a b) + Module.finrank k (Qt b c) : ℕ) :
      Cardinal) := by
    rw [← h]; push_cast; ring
  have h4 : Module.finrank k (Qt a c) = Cardinal.toNat (Module.rank k (Qt a c)) := rfl
  rw [h4, hc, Cardinal.toNat_natCast]

