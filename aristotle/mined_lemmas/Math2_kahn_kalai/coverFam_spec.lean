import RequestProject.Basic

/-!
# Covers, smallness, and Park–Pham minimum fragments
-/

namespace Math2

open Finset

variable {X : Type*} [DecidableEq X]

/-- `W` contains an edge of the hypergraph `H`, i.e. `W ∈ ⟨H⟩`. -/

lemma coverFam_spec {H : Finset (Finset X)} {W U : Finset X} {m₀ : ℕ}
    (hU : U ∈ coverFam H W m₀) : ∃ S ∈ H, m₀ < (frag H W S).card ∧ U = frag H W S := by
  simp only [coverFam, bigFam, Finset.mem_image, Finset.mem_filter] at hU
  obtain ⟨S, ⟨hSH, hbig⟩, hEq⟩ := hU
  exact ⟨S, hSH, hbig, hEq.symm⟩

