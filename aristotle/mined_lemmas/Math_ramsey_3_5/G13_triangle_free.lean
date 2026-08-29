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
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset SimpleGraph

namespace Ramsey35

variable {V : Type*} [DecidableEq V]

/-! ### Basic clique helpers -/

omit [DecidableEq V] in
/-- A finset all of whose distinct pairs are non-adjacent is a clique in the complement. -/

theorem G13_triangle_free : ¬ ∃ s : Finset (Fin 13), G13.IsNClique 3 s := by
  rintro ⟨s, hs⟩
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.1 hs.2
  rw [SimpleGraph.is3Clique_triple_iff] at hs
  exact G13_no_triangle a b c ⟨hs.1, hs.2.2, hs.2.1⟩

