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

theorem IWins_of_children_odd {A : Set (ℕ → X)} {p : List X} (hp : ¬ Even p.length)
    (hc : ∀ b : X, IWins A (p ++ [b])) : IWins A p := by
  classical
  choose σb hσb using hc
  refine ⟨fun q => σb (q.getD p.length (Classical.arbitrary X)) q, fun τ => ?_⟩
  set σ : Strategy X := fun q => σb (q.getD p.length (Classical.arbitrary X)) q with hσdef
  have hmove : nextMove σ τ p = τ p := by simp [nextMove, hp]
  have h1 : playFrom p σ τ = playFrom (p ++ [τ p]) σ τ := by
    rw [← hmove]; exact (playFrom_shift p σ τ).symm
  have h2 : playFrom (p ++ [τ p]) σ τ = playFrom (p ++ [τ p]) (σb (τ p)) τ := by
    refine playFrom_congr _ (fun q hq => ?_) (fun q _ => rfl)
    have hlen : p.length < (p ++ [τ p]).length := by simp
    have hgd : q.getD p.length (Classical.arbitrary X) = τ p := by
      rw [← getD_of_prefix hq hlen]
      simp
    show σb (q.getD p.length (Classical.arbitrary X)) q = σb (τ p) q
    rw [hgd]
  rw [h1, h2]
  exact hσb (τ p) τ

/-! ### The Gale–Stewart theorem: open games are determined -/

open Classical in
/-- A strategy for player II which, from a position not winning for player I,
moves to a position which is still not winning for player I. -/
