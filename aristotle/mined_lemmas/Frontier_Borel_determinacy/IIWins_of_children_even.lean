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

theorem IIWins_of_children_even {A : Set (ℕ → X)} {p : List X} (hp : Even p.length)
    (hc : ∀ a : X, IIWins A (p ++ [a])) : IIWins A p := by
  classical
  choose τa hτa using hc
  refine ⟨fun q => τa (q.getD p.length (Classical.arbitrary X)) q, fun σ => ?_⟩
  set τ : Strategy X := fun q => τa (q.getD p.length (Classical.arbitrary X)) q with hτdef
  have hmove : nextMove σ τ p = σ p := by simp [nextMove, hp]
  have h1 : playFrom p σ τ = playFrom (p ++ [σ p]) σ τ := by
    rw [← hmove]; exact (playFrom_shift p σ τ).symm
  have h2 : playFrom (p ++ [σ p]) σ τ = playFrom (p ++ [σ p]) σ (τa (σ p)) := by
    refine playFrom_congr _ (fun q _ => rfl) (fun q hq => ?_)
    have hlen : p.length < (p ++ [σ p]).length := by simp
    have hgd : q.getD p.length (Classical.arbitrary X) = σ p := by
      rw [← getD_of_prefix hq hlen]
      simp
    show τa (q.getD p.length (Classical.arbitrary X)) q = τa (σ p) q
    rw [hgd]
  rw [h1, h2]
  exact hτa (σ p) σ

open Classical in
/-- A strategy for player I which, from a position not winning for player II,
moves to a position which is still not winning for player II. -/
