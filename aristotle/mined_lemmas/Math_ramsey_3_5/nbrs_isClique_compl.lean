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

namespace Math

/-! ## The Ramsey property -/

/-- `RamseyProp n s t` says: every simple graph on `n` vertices contains either a clique of
size `s`, or an independent set of size `t` (a clique of size `t` in the complement).
Equivalently, every 2-colouring of the edges of `K n` has a red `K s` or a blue `K t`. -/

lemma nbrs_isClique_compl {A : Finset V} {v : V} (hv : v ∈ A) (h3 : G.CliqueFreeOn (↑A) 3) :
    Gᶜ.IsClique (↑(nbrs G A v)) := by
  intro x hx y hy hxy
  simp only [mem_coe, nbrs, mem_filter, mem_erase] at hx hy
  refine ⟨hxy, ?_⟩
  intro hadj
  refine h3 (t := {v, x, y}) ?_ ?_
  · intro z hz
    simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact hv
    · exact hx.1.2
    · exact hy.1.2
  · rw [SimpleGraph.is3Clique_triple_iff]
    exact ⟨hx.2, hy.2, hadj⟩

/-- The neighbourhood of a vertex in a triangle-free graph is small. -/
