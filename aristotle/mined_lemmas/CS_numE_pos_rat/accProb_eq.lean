/-
# Pcp Dinur
Category: Frontier Cs
Target: CS.pcp_dinur
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to precede any module docstring `/-! ... -/`, so the header
-- above is repeated below as the module docstring.)

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

/-- A *constraint graph* over the alphabet `Fin q`: a finite (multi)graph on the vertex
set `Fin numV` with `numE` edges, each edge carrying a binary constraint on the values
assigned to its endpoints.  This is the combinatorial object manipulated throughout
Dinur's proof of the PCP theorem. -/
structure ConstraintGraph (q : ℕ) where
  /-- number of vertices -/
  numV : ℕ
  /-- number of edges -/
  numE : ℕ
  /-- the endpoints of each edge -/
  edge : Fin numE → Fin numV × Fin numV
  /-- the constraint attached to each edge -/
  sat : Fin numE → (Fin q → Fin q → Bool)
  /-- constraint graphs have at least one edge -/
  edge_pos : 0 < numE

variable {q : ℕ} [NeZero q]

/-- The set of edges violated by an assignment `σ`. -/

lemma accProb_eq (G : ConstraintGraph q) (σ : Fin G.numV → Fin q) :
    ((Finset.univ.filter
        (fun e : Fin G.numE => G.sat e (σ (G.edge e).1) (σ (G.edge e).2) = true)).card : ℚ)
      / (G.numE : ℚ) = 1 - unsatFrac G σ := by
  classical
  have hsplit : (Finset.univ.filter
      (fun e : Fin G.numE => G.sat e (σ (G.edge e).1) (σ (G.edge e).2) = true)).card
      + (badEdges G σ).card = G.numE := by
    rw [badEdges]
    have := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin G.numE)))
      (p := fun e => G.sat e (σ (G.edge e).1) (σ (G.edge e).2) = true)
    simpa using this
  have hne : (G.numE : ℚ) ≠ 0 := ne_of_gt (numE_pos_rat G)
  rw [unsatFrac, eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq hne]
  exact_mod_cast hsplit

