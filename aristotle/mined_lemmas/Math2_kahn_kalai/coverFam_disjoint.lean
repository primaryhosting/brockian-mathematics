import RequestProject.Basic

/-!
# Covers, smallness, and Park–Pham minimum fragments
-/

namespace Math2

open Finset

variable {X : Type*} [DecidableEq X]

/-- `W` contains an edge of the hypergraph `H`, i.e. `W ∈ ⟨H⟩`. -/

lemma coverFam_disjoint {H : Finset (Finset X)} {W U : Finset X} {m₀ : ℕ}
    (hU : U ∈ coverFam H W m₀) : Disjoint U W := by
  obtain ⟨S, hSH, _, rfl⟩ := coverFam_spec hU
  exact frag_disjoint hSH

