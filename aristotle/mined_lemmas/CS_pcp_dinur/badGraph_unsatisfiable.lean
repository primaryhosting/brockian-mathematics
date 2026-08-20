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

theorem badGraph_unsatisfiable : ¬ badGraph.Satisfiable ∧ badGraph.unsat = 1 := by
  have hv : ∀ f, badGraph.violated f = 1 := by
    intro f; simp [ConstraintGraph.violated, badGraph]
  have hm : badGraph.minViolated = 1 := by
    simp [ConstraintGraph.minViolated, hv]
  have hs : badGraph.size = 1 := by simp [ConstraintGraph.size, badGraph]
  refine ⟨?_, ?_⟩
  · rintro ⟨f, hf⟩; rw [hv f] at hf; exact one_ne_zero hf
  · rw [ConstraintGraph.unsat, hm, hs]; norm_num

open ConstraintGraph

/-- Iterating Dinur's gap-amplification step `k` times: the size grows by at most a factor
`C ^ k`, the `UNSAT` value at least doubles each time (until it reaches the constant `α`),
and satisfiability is preserved in both directions. -/
