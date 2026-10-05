import Mathlib
import RequestProject.GaleStewartOpen

/-!
# Gale–Stewart for topologically open payoff sets

`Frontier.Gale_Stewart_open` states openness of the payoff set combinatorially (membership of a
play is guaranteed by a finite initial segment of it).  Here we record the corollary phrased with
Mathlib's product topology on `ℕ → A`.
-/

namespace Frontier

universe u

variable {A : Type u}

/-- **Gale–Stewart theorem**, topological form: if the payoff set `W` is open in the product
topology on `ℕ → A` (for instance, the product of discrete topologies), then the associated
infinite game is determined. -/

theorem gale_stewart_isOpen [Nonempty A] [TopologicalSpace A] (W : Set (ℕ → A))
    (hW : IsOpen W) :
    (∃ σ : List A → A, ∀ τ : List A → A, playSeq σ τ ∈ W) ∨
      (∃ τ : List A → A, ∀ σ : List A → A, playSeq σ τ ∉ W) := by
  refine Gale_Stewart_open (fun x => x ∈ W) ?_
  intro x hx
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.mp hW x hx
  refine ⟨I.sup id + 1, fun y hy => ?_⟩
  refine hsub fun i hi => ?_
  have hle : i ≤ I.sup id := Finset.le_sup (f := id) hi
  rw [hy i (by omega)]
  exact (hu i hi).2

end Frontier

/-!
# Gale Stewart Open
Category: Frontier — Set Theory
Target: Frontier.Gale_Stewart_open
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

universe u

variable {A : Type u}

/-- The move dictated at position `s` by the pair of strategies `(σ, τ)`:
player I (playing `σ`) moves at positions of even length, player II (playing `τ`)
moves at positions of odd length. -/
