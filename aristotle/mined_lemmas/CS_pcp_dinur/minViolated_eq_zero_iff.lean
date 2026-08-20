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
# Pcp Dinur
Category: Frontier Cs
Target: CS.pcp_dinur
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace CS

/-- A constraint graph: a finite multiset-free set of (directed) edges over `Fin numVerts`,
together with a Boolean binary constraint attached to every edge, over the alphabet
`Fin alphSize`. -/
structure ConstraintGraph where
  numVerts : ℕ
  alphSize : ℕ
  alph_pos : 0 < alphSize
  edges : Finset (Fin numVerts × Fin numVerts)
  edges_nonempty : edges.Nonempty
  sat : Fin numVerts × Fin numVerts → Fin alphSize → Fin alphSize → Bool

namespace ConstraintGraph

variable (G : ConstraintGraph)

/-- The number of edges (constraints) of `G`; the natural size measure. -/

theorem minViolated_eq_zero_iff : G.minViolated = 0 ↔ G.Satisfiable := by
  constructor
  · intro h
    obtain ⟨f, -, hf⟩ := Finset.exists_mem_eq_inf' G.assignments_nonempty G.violated
    exact ⟨f, by rw [← hf]; exact h⟩
  · rintro ⟨f, hf⟩
    exact Nat.le_zero.1 (hf ▸ Finset.inf'_le _ (Finset.mem_univ f))

