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

theorem pcp_dinur_hypotheses_consistent :
    ∃ (A : ConstraintGraph 1 → ConstraintGraph 1) (C α : ℚ),
      1 ≤ C ∧ 0 < α ∧ α ≤ 1 ∧
      (∀ G : ConstraintGraph 1, ((A G).numE : ℚ) ≤ C * (G.numE : ℚ)) ∧
      (∀ G : ConstraintGraph 1, unsat G = 0 → unsat (A G) = 0) ∧
      (∀ G : ConstraintGraph 1, min (2 * unsat G) α ≤ unsat (A G)) := by
  classical
  refine ⟨trivialAmp, 1, 1, le_rfl, one_pos, le_rfl, ?_, ?_, ?_⟩
  · intro G; simp [trivialAmp]
  · intro G h; exact unsat_trivialAmp_of_sat h
  · intro G
    by_cases h : unsat G = 0
    · rw [unsat_trivialAmp_of_sat h, h]
      simp
    · rw [unsat_trivialAmp_of_unsat h]
      exact min_le_right _ _

end CS

