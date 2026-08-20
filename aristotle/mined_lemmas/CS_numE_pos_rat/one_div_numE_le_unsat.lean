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

lemma one_div_numE_le_unsat (G : ConstraintGraph q) (h : 0 < unsat G) :
    1 / (G.numE : ℚ) ≤ unsat G := by
  obtain ⟨σ, hσ⟩ := exists_unsat_eq G
  rw [hσ] at h ⊢
  have hc : 1 ≤ ((badEdges G σ).card : ℚ) := by
    by_contra hlt
    push_neg at hlt
    have : (badEdges G σ).card = 0 := by
      have : ((badEdges G σ).card : ℚ) < 1 := hlt
      exact_mod_cast Nat.lt_one_iff.mp (by exact_mod_cast this)
    rw [unsatFrac, this] at h
    simp at h
  rw [unsatFrac]
  gcongr

end CS

namespace CS

variable {q : ℕ} [NeZero q]

section Amplification

variable (A : ConstraintGraph q → ConstraintGraph q) (C α : ℚ)

/-- Iterating the amplification step `k` times multiplies the UNSAT value by `2 ^ k`,
until it saturates at the constant `α`. -/
