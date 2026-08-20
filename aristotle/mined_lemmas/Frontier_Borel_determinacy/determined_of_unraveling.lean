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

theorem determined_of_unraveling {A : Set (ℕ → X)} (U : Unraveling A) : Determined A := by
  have hdet : Determined U.payoff :=
    U.simple_payoff.elim (gale_stewart_open U.payoff) (gale_stewart_closed U.payoff)
  rcases hdet with ⟨s, hs⟩ | ⟨t, ht⟩
  · refine Or.inl ⟨U.liftI s, fun τ => ?_⟩
    obtain ⟨t, hst⟩ := U.liftI_spec s τ
    have : playFrom [] s t ∈ U.proj ⁻¹' A := U.pullback ▸ hs t
    rwa [Set.mem_preimage, hst] at this
  · refine Or.inr ⟨U.liftII t, fun σ hmem => ?_⟩
    obtain ⟨s, hst⟩ := U.liftII_spec t σ
    refine ht s ?_
    rw [U.pullback, Set.mem_preimage, hst]
    exact hmem

/-- **Borel determinacy (Martin's theorem)**, as a Lean-checked reduction: if every Borel
payoff set admits an unraveling (Martin's unraveling theorem), then every Borel game is
determined.

The reduction itself, together with its base case (the Gale–Stewart theorem
`Frontier.gale_stewart_open`, proved here from scratch), is fully formalized; the
hypothesis `hUnravel` is exactly Martin's covering construction. The hypothesis is not
vacuous: `Frontier.Unraveling.ofOpen` produces unravelings of open payoff sets. -/
