/-!
# Pcp Dinur
Category: Frontier Cs
Target: CS.pcp_dinur
Statement: Dinur's gap-amplification proof of the PCP theorem (statement).
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

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
def size : ℕ := G.edges.card

/-- The number of constraints violated by an assignment `f`. -/
def violated (f : Fin G.numVerts → Fin G.alphSize) : ℕ :=
  (G.edges.filter (fun e => ¬ (G.sat e (f e.1) (f e.2) = true))).card

theorem assignments_nonempty :
    (Finset.univ : Finset (Fin G.numVerts → Fin G.alphSize)).Nonempty :=
  ⟨fun _ => ⟨0, G.alph_pos⟩, Finset.mem_univ _⟩

/-- The least number of constraints violated by any assignment. -/
def minViolated : ℕ :=
  (Finset.univ : Finset (Fin G.numVerts → Fin G.alphSize)).inf'
    G.assignments_nonempty G.violated

/-- The `UNSAT` value of `G`: the least possible fraction of violated constraints. -/
noncomputable def unsat : ℝ := (G.minViolated : ℝ) / (G.size : ℝ)

/-- `G` is satisfiable if some assignment violates no constraint. -/
def Satisfiable : Prop := ∃ f, G.violated f = 0

theorem size_pos : 0 < G.size :=
  Finset.card_pos.2 G.edges_nonempty

theorem violated_le_size (f : Fin G.numVerts → Fin G.alphSize) : G.violated f ≤ G.size :=
  Finset.card_filter_le _ _

theorem minViolated_le_size : G.minViolated ≤ G.size := by
  obtain ⟨f, -⟩ := G.assignments_nonempty
  exact le_trans (Finset.inf'_le _ (Finset.mem_univ f)) (G.violated_le_size f)

theorem minViolated_eq_zero_iff : G.minViolated = 0 ↔ G.Satisfiable := by
  constructor
  · intro h
    obtain ⟨f, -, hf⟩ := Finset.exists_mem_eq_inf' G.assignments_nonempty G.violated
    exact ⟨f, by rw [← hf]; exact h⟩
  · rintro ⟨f, hf⟩
    exact Nat.le_zero.1 (hf ▸ Finset.inf'_le _ (Finset.mem_univ f))

theorem unsat_nonneg : 0 ≤ G.unsat :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem unsat_le_one : G.unsat ≤ 1 := by
  rw [unsat, div_le_one (by exact_mod_cast G.size_pos)]
  exact_mod_cast G.minViolated_le_size

theorem unsat_eq_zero_iff : G.unsat = 0 ↔ G.Satisfiable := by
  rw [← G.minViolated_eq_zero_iff, unsat, div_eq_zero_iff]
  have hs : (G.size : ℝ) ≠ 0 := by exact_mod_cast G.size_pos.ne'
  simp [hs]

/-- If `G` is unsatisfiable, at least one of its `size` constraints is violated by every
assignment, so `UNSAT(G) ≥ 1 / size(G)`. -/
theorem one_div_size_le_unsat (h : ¬ G.Satisfiable) : 1 / (G.size : ℝ) ≤ G.unsat := by
  have h1 : 1 ≤ G.minViolated := Nat.one_le_iff_ne_zero.2 fun hz =>
    h (G.minViolated_eq_zero_iff.1 hz)
  have hs : (0 : ℝ) < (G.size : ℝ) := by exact_mod_cast G.size_pos
  rw [unsat, div_le_div_iff_of_pos_right hs]
  exact_mod_cast h1

end ConstraintGraph

/-- A single-edge constraint graph whose only constraint is never satisfied; it witnesses that
the definitions above are not vacuous. -/
def badGraph : ConstraintGraph where
  numVerts := 1
  alphSize := 1
  alph_pos := one_pos
  edges := {(0, 0)}
  edges_nonempty := ⟨(0, 0), by simp⟩
  sat := fun _ _ _ => false

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
theorem pcp_dinur
    (C : ℕ) (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (amp : ∀ G : ConstraintGraph, ∃ G' : ConstraintGraph,
      G'.size ≤ C * G.size ∧ min (2 * G.unsat) α ≤ G'.unsat ∧ (G.Satisfiable ↔ G'.Satisfiable))
    (G : ConstraintGraph) :
    ∃ G' : ConstraintGraph,
      G'.size ≤ C ^ (Nat.log 2 G.size + 1) * G.size ∧
      (G.Satisfiable → G'.Satisfiable) ∧
      (¬ G.Satisfiable → α ≤ G'.unsat) := by
  set k := Nat.log 2 G.size + 1 with hk
  obtain ⟨G', hsize, hgap, hsat⟩ := iterate_amplification C α hα0 amp G k
  refine ⟨G', hsize, hsat.1, fun hns => ?_⟩
  -- Since `G` is unsatisfiable, `UNSAT(G) ≥ 1 / size G`, and `2 ^ k > size G`.
  have hs : (0 : ℝ) < (G.size : ℝ) := by exact_mod_cast G.size_pos
  have hlow : 1 / (G.size : ℝ) ≤ G.unsat := G.one_div_size_le_unsat hns
  have hpow : (G.size : ℝ) < 2 ^ k := by
    have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) G.size
    exact_mod_cast this
  have hbig : α ≤ 2 ^ k * G.unsat := by
    have h1 : (1 : ℝ) ≤ 2 ^ k * (1 / (G.size : ℝ)) := by
      rw [mul_one_div, le_div_iff₀ hs, one_mul]
      exact hpow.le
    have h2 : (2 : ℝ) ^ k * (1 / (G.size : ℝ)) ≤ 2 ^ k * G.unsat := by
      have : (0 : ℝ) < 2 ^ k := by positivity
      nlinarith
    linarith
  calc α = min (2 ^ k * G.unsat) α := (min_eq_right hbig).symm
    _ ≤ G'.unsat := hgap

end CS

