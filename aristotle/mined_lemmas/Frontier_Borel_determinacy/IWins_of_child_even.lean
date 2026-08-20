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

theorem IWins_of_child_even {A : Set (ℕ → X)} {p : List X} (hp : Even p.length) {a : X}
    (hc : IWins A (p ++ [a])) : IWins A p := by
  classical
  obtain ⟨σa, hσa⟩ := hc
  refine ⟨fun q => if q = p then a else σa q, fun τ => ?_⟩
  set σ : Strategy X := fun q => if q = p then a else σa q with hσdef
  have hmove : nextMove σ τ p = a := by simp [nextMove, hp, hσdef]
  have h1 : playFrom p σ τ = playFrom (p ++ [a]) σ τ := by
    rw [← hmove]; exact (playFrom_shift p σ τ).symm
  have h2 : playFrom (p ++ [a]) σ τ = playFrom (p ++ [a]) σa τ := by
    refine playFrom_congr _ (fun q hq => ?_) (fun q _ => rfl)
    have hne : q ≠ p := by
      rintro rfl
      have := hq.length_le
      simp at this
    simp [hσdef, hne]
  rw [h1, h2]
  exact hσa τ

