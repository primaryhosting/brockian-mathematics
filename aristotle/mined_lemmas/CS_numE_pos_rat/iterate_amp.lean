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

lemma iterate_amp (hα0 : 0 < α)
    (hamp : ∀ G : ConstraintGraph q, min (2 * unsat G) α ≤ unsat (A G))
    (k : ℕ) (G : ConstraintGraph q) :
    min (2 ^ k * unsat G) α ≤ unsat (A^[k] G) := by
  induction k generalizing G with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply]
      have h1 : min (2 ^ k * unsat (A G)) α ≤ unsat (A^[k] (A G)) := ih (A G)
      have h2 : min (2 * unsat G) α ≤ unsat (A G) := hamp G
      refine le_trans ?_ h1
      rcases le_total (2 * unsat G) α with h | h
      · have : min (2 * unsat G) α = 2 * unsat G := min_eq_left h
        rw [this] at h2
        have : (2 : ℚ) ^ (k + 1) * unsat G ≤ 2 ^ k * unsat (A G) := by
          have hk : (0 : ℚ) ≤ 2 ^ k := by positivity
          calc (2 : ℚ) ^ (k + 1) * unsat G = 2 ^ k * (2 * unsat G) := by ring
            _ ≤ 2 ^ k * unsat (A G) := by nlinarith
        exact min_le_min this le_rfl
      · have hmin : min (2 * unsat G) α = α := min_eq_right h
        rw [hmin] at h2
        have hk1 : (1 : ℚ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
        have : α ≤ 2 ^ k * unsat (A G) := by nlinarith
        calc min ((2 : ℚ) ^ (k + 1) * unsat G) α ≤ α := min_le_right _ _
          _ ≤ min (2 ^ k * unsat (A G)) α := le_min this le_rfl

/-- Iterating a satisfiability-preserving step preserves satisfiability. -/
