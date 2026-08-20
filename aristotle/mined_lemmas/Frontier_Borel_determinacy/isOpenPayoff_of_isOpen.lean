import Mathlib
/-!
# Borel Determinacy
Category: Frontier — Set Theory
Target: Frontier.Borel_determinacy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

universe u

namespace Frontier

variable {X : Type u}

/-- A strategy assigns a move to every finite position of the game. -/
abbrev Strategy (X : Type u) := List X → X

/-- The move played at position `q`: player I (resp. II) moves at positions of
even (resp. odd) length. -/

theorem isOpenPayoff_of_isOpen {A : Set (ℕ → X)} (hA : IsOpen A) : IsOpenPayoff A := by
  intro x hx
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.mp hA x hx
  refine ⟨(I.sup id) + 1, fun y hy => ?_⟩
  refine hsub (fun i hi => ?_)
  have hlt : i < (I.sup id) + 1 := lt_of_le_of_lt (Finset.le_sup (f := id) hi) (by omega)
  rw [hy i hlt]
  exact (hu i hi).2

/-- **Gale–Stewart theorem, topological form**: a game whose payoff set is open in the
product topology on `ℕ → X` is determined. (In the intended descriptive-set-theoretic
setting `X` carries the discrete topology, so that `ℕ → X` is a Baire space.) -/
