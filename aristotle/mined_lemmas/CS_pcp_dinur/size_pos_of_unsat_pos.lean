/-
# Pcp Dinur
Category: Frontier Cs
Target: CS.pcp_dinur
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Pcp Dinur
Category: Frontier Cs
Target: CS.pcp_dinur
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace CS

/-- A *constraint graph* over the alphabet `α`: a finite vertex set `Fin numVerts`
together with a list of edges, each carrying a binary constraint on `α`.  This is the
combinatorial object (a binary CSP instance) manipulated by Dinur's proof of the PCP
theorem. -/
structure ConstraintGraph (α : Type) where
  /-- Number of vertices; the vertex set is `Fin numVerts`. -/
  numVerts : ℕ
  /-- The edges, each with its constraint. -/
  edges : List (Fin numVerts × Fin numVerts × (α → α → Bool))

namespace ConstraintGraph

variable {α : Type}

/-- The size of a constraint graph is its number of edges. -/

theorem size_pos_of_unsat_pos (G : ConstraintGraph α) (h : 0 < G.unsat) : 0 < G.size := by
  rcases Nat.eq_zero_or_pos G.size with hs | hs
  · obtain ⟨f, hf⟩ := G.exists_unsat_eq
    rw [hf] at h
    unfold unsatFrac at h
    rw [hs] at h
    simp at h
  · exact hs

/-- If a constraint graph is unsatisfiable, then at least one of its `size G` edges
is violated by every assignment, so `UNSAT(G) ≥ 1 / size G`. -/
