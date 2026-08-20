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

theorem iterate_amplification
    (C : ℕ) (α : ℝ) (hα0 : 0 < α)
    (amp : ∀ G : ConstraintGraph, ∃ G' : ConstraintGraph,
      G'.size ≤ C * G.size ∧ min (2 * G.unsat) α ≤ G'.unsat ∧ (G.Satisfiable ↔ G'.Satisfiable))
    (G : ConstraintGraph) (k : ℕ) :
    ∃ G' : ConstraintGraph, G'.size ≤ C ^ k * G.size ∧
      min (2 ^ k * G.unsat) α ≤ G'.unsat ∧ (G.Satisfiable ↔ G'.Satisfiable) := by
  induction k with
  | zero => exact ⟨G, by simp, by simp, Iff.rfl⟩
  | succ k ih =>
      obtain ⟨Gk, hsize, hgap, hsat⟩ := ih
      obtain ⟨G', hsize', hgap', hsat'⟩ := amp Gk
      refine ⟨G', ?_, ?_, hsat.trans hsat'⟩
      · calc G'.size ≤ C * Gk.size := hsize'
          _ ≤ C * (C ^ k * G.size) := Nat.mul_le_mul_left _ hsize
          _ = C ^ (k + 1) * G.size := by ring
      · refine le_trans ?_ hgap'
        refine le_min ?_ (min_le_right _ _)
        have hnn := Gk.unsat_nonneg
        have hleft : min (2 ^ (k + 1) * G.unsat) α ≤ 2 ^ (k + 1) * G.unsat := min_le_left _ _
        have hright : min (2 ^ (k + 1) * G.unsat) α ≤ α := min_le_right _ _
        have hpow : (2 : ℝ) ^ (k + 1) * G.unsat = 2 * (2 ^ k * G.unsat) := by ring
        rcases le_total (2 ^ k * G.unsat) α with h | h
        · rw [min_eq_left h] at hgap; linarith
        · rw [min_eq_right h] at hgap; linarith

/-- **Dinur's gap amplification proof of the PCP theorem** (the reduction from the Main
Theorem to the Main Lemma).

Hypothesis `amp` is Dinur's Main Lemma: there are constants `C ≥ 1` and `α ∈ (0,1]` and a
transformation of constraint graphs `G ↦ G'` which blows up the size by at most a factor `C`,
preserves satisfiability (in both directions), and at least doubles the `UNSAT` value as long
as it is below `α`.

Conclusion (the PCP theorem in the constraint-graph formulation): applying the transformation
`O(log (size G))` times yields a graph `G'` of size polynomial in `size G` such that
satisfiable instances stay satisfiable, while unsatisfiable instances acquire a constant gap:
`UNSAT(G') ≥ α`. -/
