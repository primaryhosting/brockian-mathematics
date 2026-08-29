-- (Lean requires `import` to be the first command of a file, so the header comment
-- follows it.)
import Mathlib

/-!
# Dijkstra Correct
Category: Computer Science
Target: CS.dijkstra_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
We formalise Dijkstra's algorithm on a finite directed graph whose edge weights are
nonnegative (encoded by taking values in `ℝ≥0∞`, where `⊤` means "no edge"), and prove
that it computes the true shortest-path distances from a fixed source.
-/

namespace CS

open scoped ENNReal

variable {V : Type*}

/-! ## Walks, their weights, and the shortest-path distance -/

/-- The endpoint of the walk that starts at `s` and visits the vertices of `l` in order. -/

lemma exists_split (S : Finset V) :
    ∀ (l : List V), (∃ v ∈ l, v ∉ S) →
      ∃ (l₁ : List V) (x : V) (l₂ : List V),
        l = l₁ ++ x :: l₂ ∧ (∀ y ∈ l₁, y ∈ S) ∧ x ∉ S := by
  intro l
  induction l with
  | nil => rintro ⟨v, hv, -⟩; simp at hv
  | cons a t ih =>
      intro h
      by_cases ha : a ∈ S
      · obtain ⟨v, hv, hvS⟩ := h
        rcases List.mem_cons.1 hv with rfl | hv'
        · exact absurd ha hvS
        · obtain ⟨l₁, x, l₂, rfl, h₁, h₂⟩ := ih ⟨v, hv', hvS⟩
          exact ⟨a :: l₁, x, l₂, by simp, by
            intro y hy
            rcases List.mem_cons.1 hy with rfl | hy'
            · exact ha
            · exact h₁ y hy', h₂⟩
      · exact ⟨[], a, t, by simp, by simp, ha⟩

/-! ## The algorithm -/

/-- The state of Dijkstra's algorithm: a set `S` of settled vertices and tentative
distances `D`. -/
structure State (V : Type*) where
  /-- the settled vertices -/
  S : Finset V
  /-- the tentative distances -/
  D : V → ℝ≥0∞

/-- A vertex of `T` minimising `D`. -/
