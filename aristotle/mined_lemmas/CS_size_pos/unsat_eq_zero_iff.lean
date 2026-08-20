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

/-- A *constraint graph* over the alphabet `Fin q`: a finite nonempty list (multiset) of
constraints, each of which is a pair of vertices together with a boolean predicate on the
pair of values assigned to them. -/
structure ConstraintGraph (q : ℕ) where
  /-- Number of vertices. -/
  numVerts : ℕ
  /-- The constraints (edges): a pair of endpoints and a boolean relation on their values. -/
  edges : List (Fin numVerts × Fin numVerts × (Fin q → Fin q → Bool))
  /-- Constraint graphs have at least one constraint. -/
  edges_ne : edges ≠ []

namespace ConstraintGraph

variable {q : ℕ} [NeZero q]

/-- The size of a constraint graph is its number of constraints. -/

lemma unsat_eq_zero_iff (G : ConstraintGraph q) : G.unsat = 0 ↔ G.Satisfiable := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := G.exists_unsat_eq
    exact ⟨a, (G.unsatFrac_eq_zero_iff a).mp (by rw [← ha, h])⟩
  · rintro ⟨a, ha⟩
    refine le_antisymm ?_ G.unsat_nonneg
    have := G.unsat_le a
    rwa [(G.unsatFrac_eq_zero_iff a).mpr ha] at this

/-- The base gap: an unsatisfiable constraint graph violates at least one out of its `size`
constraints, i.e. `UNSAT(G) ≥ 1 / size G`. -/
