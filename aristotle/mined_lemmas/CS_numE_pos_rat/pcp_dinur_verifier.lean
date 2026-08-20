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

theorem pcp_dinur_verifier
    (A : ConstraintGraph q → ConstraintGraph q) (C α : ℚ)
    (hC : 1 ≤ C) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (t : ℕ) (hCt : C ≤ 2 ^ t)
    (hsize : ∀ G : ConstraintGraph q, ((A G).numE : ℚ) ≤ C * (G.numE : ℚ))
    (hsat : ∀ G : ConstraintGraph q, unsat G = 0 → unsat (A G) = 0)
    (hamp : ∀ G : ConstraintGraph q, min (2 * unsat G) α ≤ unsat (A G))
    (G : ConstraintGraph q) :
    ∃ H : ConstraintGraph q,
      H = A^[Nat.clog 2 G.numE] G ∧
      ((H.numE : ℚ) ≤ (2 * (G.numE : ℚ)) ^ t * (G.numE : ℚ)) ∧
      (unsat G = 0 → ∃ σ : Fin H.numV → Fin q,
        ((Finset.univ.filter
          (fun e : Fin H.numE => H.sat e (σ (H.edge e).1) (σ (H.edge e).2) = true)).card : ℚ)
            / (H.numE : ℚ) = 1) ∧
      (0 < unsat G → ∀ σ : Fin H.numV → Fin q,
        ((Finset.univ.filter
          (fun e : Fin H.numE => H.sat e (σ (H.edge e).1) (σ (H.edge e).2) = true)).card : ℚ)
            / (H.numE : ℚ) ≤ 1 - α) := by
  classical
  obtain ⟨H, hH, hcomp, hsound, hsz⟩ :=
    pcp_dinur A C α hC hα0 hα1 t hCt hsize hsat hamp G
  refine ⟨H, hH, hsz, ?_, ?_⟩
  · intro h0
    obtain ⟨σ, hσ⟩ := exists_unsat_eq H
    refine ⟨σ, ?_⟩
    rw [accProb_eq, ← hσ, hcomp h0, sub_zero]
  · intro hpos σ
    have h1 : α ≤ unsat H := hsound hpos
    have h2 : unsat H ≤ unsatFrac H σ := unsat_le_unsatFrac H σ
    rw [accProb_eq]
    linarith


/-!
### Non-vacuity of the hypotheses

The amplification step `A` is the deep content of Dinur's proof; here we merely record
that the hypothesis package of `CS.pcp_dinur` is consistent, so that the theorem is not
vacuous, by exhibiting a (degenerate) amplification step over the one-letter alphabet.
-/

