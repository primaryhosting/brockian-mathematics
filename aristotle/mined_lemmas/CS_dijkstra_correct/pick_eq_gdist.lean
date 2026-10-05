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

lemma pick_eq_gdist (w : V → V → ℝ≥0∞) (s : V) {st : State V} (hst : Inv w s st)
    (h : st.Sᶜ.Nonempty) : st.D (pick st.D st.Sᶜ h) = gdist w s (pick st.D st.Sᶜ h) := by
  set u := pick st.D st.Sᶜ h with hu
  have huS : u ∉ st.S := by
    have := pick_mem st.D st.Sᶜ h
    simpa using this
  refine le_antisymm ?_ (hst.ge u)
  refine le_gdist w ?_
  intro l hl
  have hlne : l ≠ [] := by
    rintro rfl
    exact huS (by simpa [hl.symm] using hst.src)
  have hmem : ∃ v ∈ l, v ∉ st.S := ⟨u, hl ▸ endp_mem s hlne, huS⟩
  obtain ⟨l₁, x, l₂, rfl, h₁, hx⟩ := exists_split st.S l hmem
  set y := endp s l₁ with hy
  have hyS : y ∈ st.S := by
    rcases eq_or_ne l₁ [] with rfl | hne
    · simpa [hy] using hst.src
    · exact h₁ _ (endp_mem s hne)
  calc st.D u ≤ st.D x := pick_min st.D st.Sᶜ h x (by simpa using hx)
    _ ≤ gdist w s y + w y x := hst.relax y hyS x hx
    _ ≤ wt w s l₁ + w y x := add_le_add (gdist_le w rfl) le_rfl
    _ ≤ wt w s l₁ + (w y x + wt w x l₂) := add_le_add le_rfl le_self_add
    _ = wt w s (l₁ ++ x :: l₂) := by rw [wt_append]; rfl

