import Mathlib

/-!
# Huh Matroid Log Concave
Category: Frontier — Fields Medal Work
Target: Frontier.huh_matroid_log_concave
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


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

set_option grind.warning false

namespace Frontier

open Polynomial

variable {α : Type*}

/-- The natural-number rank function of a matroid. -/

theorem mrk_freeOn_ground [Fintype α] :
    mrk (Matroid.freeOn (Set.univ : Set α)) Set.univ = Fintype.card α := by
  rw [mrk_freeOn_univ, ← Finset.coe_univ, Set.encard_coe_eq_coe_finsetCard]
  simp

/-! ### The characteristic polynomial of the Boolean (free) matroid -/

