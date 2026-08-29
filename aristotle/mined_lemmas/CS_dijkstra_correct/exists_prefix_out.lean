import Mathlib

/-!
# Dijkstra Correct
Category: Computer Science
Target: CS.dijkstra_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

open scoped ENNReal

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `wcost w u l` is the total weight of the walk that starts at `u` and visits the
vertices of `l` in order. -/

lemma exists_prefix_out {w : V → V → ℝ≥0∞} {S : Finset V} :
    ∀ (l : List V) (x : V), endpt x l ∉ S →
      ∃ l₁ : List V, InS S x l₁ ∧ endpt x l₁ ∉ S ∧ wcost w x l₁ ≤ wcost w x l := by
  intro l
  induction l with
  | nil => intro x hx; exact ⟨[], trivial, hx, le_rfl⟩
  | cons a l ih =>
      intro x hx
      by_cases hxS : x ∈ S
      · obtain ⟨l₁, h1, h2, h3⟩ := ih a hx
        refine ⟨a :: l₁, ⟨hxS, h1⟩, h2, ?_⟩
        simp only [wcost]
        gcongr
      · exact ⟨[], trivial, hxS, by simp [wcost]⟩

omit [Fintype V] [DecidableEq V] in
/-- Sanity check: the distance is bounded by the weight of a single edge. -/
