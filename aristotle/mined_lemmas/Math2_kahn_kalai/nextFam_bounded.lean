import RequestProject.Basic

/-!
# Covers, smallness, and Park–Pham minimum fragments
-/

namespace Math2

open Finset

variable {X : Type*} [DecidableEq X]

/-- `W` contains an edge of the hypergraph `H`, i.e. `W ∈ ⟨H⟩`. -/

lemma nextFam_bounded {H : Finset (Finset X)} {W : Finset X} {m₀ : ℕ} :
    ∀ T ∈ nextFam H W m₀, T.card ≤ m₀ := by
  intro T hT
  simp only [nextFam, Finset.mem_image, Finset.mem_filter] at hT
  obtain ⟨S, ⟨_, hcard⟩, hEq⟩ := hT
  rw [← hEq]; exact hcard

