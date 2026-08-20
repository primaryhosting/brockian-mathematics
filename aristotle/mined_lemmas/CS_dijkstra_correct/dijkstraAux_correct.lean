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

lemma dijkstraAux_correct (w : V → V → ℝ≥0∞) (s : V) :
    ∀ (n : ℕ) (T : Finset V) (d : V → ℝ≥0∞), T.card ≤ n →
      (∀ v, d v = rdist w Tᶜ s v) → (∀ z ∈ Tᶜ, rdist w Tᶜ s z = gdist w s z) →
      ∀ v, dijkstraAux w n T d v = gdist w s v := by
  intro n
  induction n with
  | zero =>
      intro T d hcard h1 _ v
      have hT : T = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
      subst hT
      simpa [dijkstraAux, rdist_univ] using h1 v
  | succ n ih =>
      intro T d hcard h1 h2 v
      by_cases hT : T.Nonempty
      · set u := pick d T hT with hu
        have huT : u ∈ T := pick_mem d T hT
        have huS : u ∉ Tᶜ := by simpa using huT
        -- `u` minimises the restricted distance among unsettled vertices
        have hmin : ∀ x, x ∉ Tᶜ → rdist w Tᶜ s u ≤ rdist w Tᶜ s x := by
          intro x hx
          have hxT : x ∈ T := by simpa using hx
          have := pick_min d T hT x hxT
          rwa [h1, h1] at this
        have hex : rdist w Tᶜ s u = gdist w s u :=
          rdist_eq_gdist_of_min w Tᶜ s u huS hmin
        have hcompl : (T.erase u)ᶜ = insert u Tᶜ := by
          ext x; by_cases hxu : x = u <;> simp [hxu, huT]
        have hstep : ∀ x, min (d x) (d u + w u x) = rdist w (T.erase u)ᶜ s x := by
          intro x
          rw [hcompl, rdist_insert w Tᶜ s u hex h2 x, h1, h1]
        have hcard' : (T.erase u).card ≤ n := by
          have := Finset.card_erase_of_mem huT
          have hpos : 0 < T.card := Finset.card_pos.mpr hT
          omega
        have h2' : ∀ z ∈ (T.erase u)ᶜ, rdist w (T.erase u)ᶜ s z = gdist w s z := by
          intro z hz
          rw [hcompl] at hz ⊢
          refine le_antisymm ?_ (gdist_le_rdist w _ s z)
          rcases Finset.mem_insert.mp hz with rfl | hzS
          · exact (rdist_mono w (Finset.subset_insert u Tᶜ) s _).trans hex.le
          · exact (rdist_mono w (Finset.subset_insert u Tᶜ) s z).trans (h2 z hzS).le
        have := ih (T.erase u) (fun x => min (d x) (d u + w u x)) hcard'
          (fun x => hstep x) h2' v
        rw [dijkstraAux, dif_pos hT]
        exact this
      · have hT' : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
        subst hT'
        rw [dijkstraAux, dif_neg hT]
        simpa [rdist_univ] using h1 v

/-- **Dijkstra's algorithm is correct**: on a finite graph with nonnegative edge weights
(encoded as `w : V → V → ℝ≥0∞`, with `⊤` meaning "no edge"), the array computed by
Dijkstra's algorithm from the source `s` gives, at every vertex `t`, the shortest-path
distance from `s` to `t`, i.e. the infimum of the costs of all walks from `s` to `t`. -/
