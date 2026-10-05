import RequestProject.Basic

/-!
# Covers, smallness, and Park–Pham minimum fragments
-/

namespace Math2

open Finset

variable {X : Type*} [DecidableEq X]

/-- `W` contains an edge of the hypergraph `H`, i.e. `W ∈ ⟨H⟩`. -/

lemma nextFam_subset_ground {H : Finset (Finset X)} {W V : Finset X} {m₀ : ℕ}
    (hV : ∀ S ∈ H, S ⊆ V) : ∀ T ∈ nextFam H W m₀, T ⊆ V := by
  intro T hT
  simp only [nextFam, Finset.mem_image, Finset.mem_filter] at hT
  obtain ⟨S, ⟨hSH, _⟩, hEq⟩ := hT
  rw [← hEq]
  exact (frag_subset hSH).trans (hV S hSH)

/-- Capture property for the next-round hypergraph. -/
