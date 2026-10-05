import RequestProject.Basic

/-!
# Covers, smallness, and Park–Pham minimum fragments
-/

namespace Math2

open Finset

variable {X : Type*} [DecidableEq X]

/-- `W` contains an edge of the hypergraph `H`, i.e. `W ∈ ⟨H⟩`. -/

lemma coverFam_subset_ground {V : Finset X} {H : Finset (Finset X)} {W U : Finset X} {m₀ : ℕ}
    (hV : ∀ S ∈ H, S ⊆ V) (hU : U ∈ coverFam H W m₀) : U ⊆ V := by
  obtain ⟨S, hSH, _, rfl⟩ := coverFam_spec hU
  exact (frag_subset hSH).trans (hV S hSH)

