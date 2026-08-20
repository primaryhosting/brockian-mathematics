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

theorem IIWins_of_child_odd {A : Set (ℕ → X)} {p : List X} (hp : ¬ Even p.length) {b : X}
    (hc : IIWins A (p ++ [b])) : IIWins A p := by
  classical
  obtain ⟨τb, hτb⟩ := hc
  refine ⟨fun q => if q = p then b else τb q, fun σ => ?_⟩
  set τ : Strategy X := fun q => if q = p then b else τb q with hτdef
  have hmove : nextMove σ τ p = b := by simp [nextMove, hp, hτdef]
  have h1 : playFrom p σ τ = playFrom (p ++ [b]) σ τ := by
    rw [← hmove]; exact (playFrom_shift p σ τ).symm
  have h2 : playFrom (p ++ [b]) σ τ = playFrom (p ++ [b]) σ τb := by
    refine playFrom_congr _ (fun q _ => rfl) (fun q hq => ?_)
    have hne : q ≠ p := by
      rintro rfl
      have := hq.length_le
      simp at this
    simp [hτdef, hne]
  rw [h1, h2]
  exact hτb σ

