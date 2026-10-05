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

lemma local_index_aux (P : Place) (m : ℤ) (d : ℕ) :
    Module.Finite k (Qt (V.Kge P (m + d)) (V.Kge P m)) ∧
      Module.finrank k (Qt (V.Kge P (m + d)) (V.Kge P m)) = d * V.degP P := by
  induction d with
  | zero =>
      rw [Nat.cast_zero, add_zero]
      exact ⟨finite_Qt_self (k := k) (V.Kge P m), by
        rw [finrank_Qt_self (k := k) (V.Kge P m)]; ring⟩
  | succ d ih =>
      obtain ⟨hfd, hrd⟩ := ih
      have hle1 : V.Kge P (m + d + 1) ≤ V.Kge P (m + d) := V.Kge_mono (by omega)
      have hle2 : V.Kge P (m + d) ≤ V.Kge P m := V.Kge_mono (by omega)
      have hf1 : Module.Finite k (Qt (V.Kge P (m + d + 1)) (V.Kge P (m + d))) :=
        finite_Qt_Kge_succ V hfin P (m + d)
      have hr1 : Module.finrank k (Qt (V.Kge P (m + d + 1)) (V.Kge P (m + d))) = V.degP P :=
        finrank_Qt_Kge_succ V hfin P (m + d)
      have heq : m + ((d : ℤ) + 1) = m + d + 1 := by ring
      constructor
      · rw [show ((d + 1 : ℕ) : ℤ) = (d : ℤ) + 1 by push_cast; ring, heq]
        exact finite_Qt_of_both hle1 hle2
      · rw [show ((d + 1 : ℕ) : ℤ) = (d : ℤ) + 1 by push_cast; ring, heq]
        rw [← finrank_Qt_add hle1 hle2, hr1, hrd]
        ring

