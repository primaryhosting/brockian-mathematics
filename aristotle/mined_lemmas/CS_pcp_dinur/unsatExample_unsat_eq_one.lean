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

theorem unsatExample_unsat_eq_one : unsatExample.unsat = 1 := by
  have h : ∀ f : Fin unsatExample.numVerts → Bool, unsatExample.unsatFrac f = 1 := by
    intro f
    simp [unsatFrac, unsatCount, unsatExample, ConstraintGraph.size]
  refine le_antisymm ?_ ?_
  · obtain ⟨f⟩ : Nonempty (Fin unsatExample.numVerts → Bool) := inferInstance
    calc unsatExample.unsat ≤ unsatExample.unsatFrac f :=
          Finset.inf'_le _ (Finset.mem_univ f)
      _ = 1 := h f
  · exact Finset.le_inf' _ _ fun f _ => le_of_eq (h f).symm

/-- Non-vacuity check for the hypotheses of `CS.pcp_dinur`: for every gap constant
`0 < a ≤ 1` there really is an operation on constraint graphs satisfying the three
assumptions of the amplification lemma (with `C = 1`).  (Of course the interest of
Dinur's actual amplification lemma lies in the *efficient computability* of `amp`,
which is not modelled here; this lemma only certifies that the hypotheses below are
consistent, so that `CS.pcp_dinur` is not vacuously true.) -/
