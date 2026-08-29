import RequestProject.Basic

/-!
# Covers, smallness, and Park–Pham minimum fragments
-/

namespace Math2

open Finset

variable {X : Type*} [DecidableEq X]

/-- `W` contains an edge of the hypergraph `H`, i.e. `W ∈ ⟨H⟩`. -/

lemma nextFam_capture {H : Finset (Finset X)} {W : Finset X} {m₀ : ℕ}
    {T : Finset X} (hT : T ∈ nextFam H W m₀) : ∃ S' ∈ H, S' ⊆ W ∪ T := by
  simp only [nextFam, Finset.mem_image, Finset.mem_filter] at hT
  obtain ⟨S, ⟨hSH, _⟩, hEq⟩ := hT
  rw [← hEq]
  exact frag_capture hSH

/-- If the next-round hypergraph is covered by `W₂` then `H` is covered by `W ∪ W₂`. -/
