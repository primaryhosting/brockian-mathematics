import RequestProject.Basic

/-!
# Covers, smallness, and Park–Pham minimum fragments
-/

namespace Math2

open Finset

variable {X : Type*} [DecidableEq X]

/-- `W` contains an edge of the hypergraph `H`, i.e. `W ∈ ⟨H⟩`. -/

lemma coverFam_subset_pick {H : Finset (Finset X)} {W U : Finset X} {m₀ : ℕ}
    (hU : U ∈ coverFam H W m₀) : U ⊆ pick H (W ∪ U) := by
  obtain ⟨S, hSH, _, rfl⟩ := coverFam_spec hU
  have hcov : Covers H (W ∪ frag H W S) := frag_capture hSH
  obtain ⟨hmem, hsub⟩ := pick_mem hcov
  exact frag_key hSH hmem hsub

