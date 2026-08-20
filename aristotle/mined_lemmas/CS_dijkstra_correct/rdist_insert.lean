import Mathlib

/-!
# Dijkstra Correct
Category: Computer Science
Target: CS.dijkstra_correct
Statement: Dijkstra's algorithm computes shortest-path distances on nonnegative-weight graphs.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped ENNReal

namespace CS

variable {V : Type*}

/-! ## Walks, their costs, and shortest-path distances

A weighted directed graph on the vertex type `V` is given by a weight function
`w : V → V → ℝ≥0∞`.  Values in `ℝ≥0∞` are automatically nonnegative (this is the
"nonnegative weights" hypothesis), and `w u v = ⊤` encodes the absence of an edge
from `u` to `v`.

A walk starting at `s` is described by the list `l` of the vertices it visits after `s`. -/

/-- The endpoint of the walk that starts at `s` and visits the vertices of `l` in order. -/

lemma rdist_insert (w : V → V → ℝ≥0∞) (S : Finset V) (s u : V)
    (hex : rdist w S s u = gdist w s u)
    (hA : ∀ z ∈ S, rdist w S s z = gdist w s z) (v : V) :
    rdist w (insert u S) s v = min (rdist w S s v) (rdist w S s u + w u v) := by
  refine le_antisymm (le_min (rdist_mono w (Finset.subset_insert u S) s v) ?_) ?_
  · calc rdist w (insert u S) s v
        ≤ rdist w (insert u S) s u + w u v :=
          rdist_extend w (Finset.mem_insert_self u S) s v
      _ ≤ rdist w S s u + w u v :=
          add_le_add (rdist_mono w (Finset.subset_insert u S) s u) le_rfl
  · refine le_rdist fun l hl hr => ?_
    rcases List.eq_nil_or_concat l with rfl | ⟨L, b, rfl⟩
    · simp only [endpt_nil] at hl
      subst hl
      simp [rdist_self]
    · simp only [List.concat_eq_append] at hl hr ⊢
      have hb : b = v := by rw [endpt_append] at hl; simpa using hl
      subst hb
      rw [Restr_append] at hr
      obtain ⟨hL, hz⟩ := hr
      have hzS : endpt s L ∈ insert u S := by simpa using hz.1
      have hcost : cost w s (L ++ [b]) = cost w s L + w (endpt s L) b := by
        rw [cost_append, cost_cons, cost_nil, add_zero]
      rw [hcost]
      rcases Finset.mem_insert.mp hzS with hzu | hzS'
      · rw [hzu]
        refine le_trans (min_le_right _ _) (add_le_add ?_ le_rfl)
        rw [hex]
        exact gdist_le_cost hzu
      · refine le_trans (min_le_left _ _) ?_
        calc rdist w S s b ≤ rdist w S s (endpt s L) + w (endpt s L) b :=
              rdist_extend w hzS' s b
          _ ≤ cost w s L + w (endpt s L) b := by
              refine add_le_add ?_ le_rfl
              rw [hA _ hzS']
              exact gdist_le_cost rfl

/-! ## The algorithm -/

variable [Fintype V]

open Classical in
/-- The unsettled vertex with minimal tentative distance (the vertex extracted from the
priority queue). -/
