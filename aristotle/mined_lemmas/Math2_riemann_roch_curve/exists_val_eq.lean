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

lemma exists_val_eq (P : Place) (m : ℤ) : ∃ u : K, u ≠ 0 ∧ V.v P u = m := by
  obtain ⟨t, ht0, ht⟩ := V.exists_uniformizer P
  rcases le_or_gt 0 m with h | h
  · refine ⟨t ^ m.toNat, pow_ne_zero _ ht0, ?_⟩
    rw [V.v_pow P ht0, ht, mul_one]
    omega
  · refine ⟨(t ^ (-m).toNat)⁻¹, inv_ne_zero (pow_ne_zero _ ht0), ?_⟩
    rw [V.v_inv P (pow_ne_zero _ ht0), V.v_pow P ht0, ht, mul_one]
    omega

/-! ### Multiplication by a nonzero element -/

/-- Multiplication by a nonzero element of `K`, as a `k`-linear automorphism. -/
