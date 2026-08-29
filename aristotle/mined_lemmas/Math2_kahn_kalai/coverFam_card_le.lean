import RequestProject.Basic

/-!
# Covers, smallness, and Park–Pham minimum fragments
-/

namespace Math2

open Finset

variable {X : Type*} [DecidableEq X]

/-- `W` contains an edge of the hypergraph `H`, i.e. `W ∈ ⟨H⟩`. -/

lemma coverFam_card_le {H : Finset (Finset X)} {ℓ : ℕ} (hbd : ∀ S ∈ H, S.card ≤ ℓ)
    {W U : Finset X} {m₀ : ℕ} (hU : U ∈ coverFam H W m₀) : U.card ≤ ℓ := by
  obtain ⟨S, hSH, _, rfl⟩ := coverFam_spec hU
  exact (frag_card_le hSH).trans (hbd S hSH)

/-- Members of the one-round cover are contained in the chosen edge of `W ∪ U`. -/
