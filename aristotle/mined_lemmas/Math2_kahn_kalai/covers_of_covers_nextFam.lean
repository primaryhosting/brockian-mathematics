import RequestProject.Basic

/-!
# Covers, smallness, and Park–Pham minimum fragments
-/

namespace Math2

open Finset

variable {X : Type*} [DecidableEq X]

/-- `W` contains an edge of the hypergraph `H`, i.e. `W ∈ ⟨H⟩`. -/

lemma covers_of_covers_nextFam {H : Finset (Finset X)} {W W₂ : Finset X} {m₀ : ℕ}
    (h : Covers (nextFam H W m₀) W₂) : Covers H (W ∪ W₂) := by
  obtain ⟨T, hT, hTW₂⟩ := h
  obtain ⟨S', hS'H, hS'sub⟩ := nextFam_capture hT
  exact ⟨S', hS'H, hS'sub.trans (Finset.union_subset_union_right hTW₂)⟩

/-- A cover of the next-round hypergraph, together with the round's cover, covers `H`. -/
