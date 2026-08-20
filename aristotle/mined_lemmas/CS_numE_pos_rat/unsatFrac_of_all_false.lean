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

lemma unsatFrac_of_all_false (G : ConstraintGraph q)
    (h : ∀ (e : Fin G.numE) (a b : Fin q), G.sat e a b = false) (σ : Fin G.numV → Fin q) :
    unsatFrac G σ = 1 := by
  have hb : badEdges G σ = Finset.univ := by
    apply Finset.filter_true_of_mem
    intro e _
    simp [h e]
  have : ((badEdges G σ).card : ℚ) = (G.numE : ℚ) := by
    rw [hb]; simp
  rw [unsatFrac, this]
  exact div_self (ne_of_gt (numE_pos_rat G))

/-- A degenerate amplification step over the one-letter alphabet: it keeps satisfiable
instances satisfiable and sends unsatisfiable instances to instances with UNSAT value `1`. -/
