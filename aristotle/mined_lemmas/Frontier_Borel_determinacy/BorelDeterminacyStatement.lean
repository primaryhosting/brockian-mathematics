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

def BorelDeterminacyStatement (X : Type u) [Nonempty X] [TopologicalSpace X] : Prop :=
  ∀ A : Set (ℕ → X), IsBorelPayoff A → Determined A

/-! ### Unravelings (Martin coverings) and the reduction to the open case -/

/-- An *unraveling* of a payoff set `A ⊆ ℕ → X` (an abstract form of a Martin covering
whose covering game has clopen payoff): an auxiliary game on moves `Y` whose payoff set
`payoff` is topologically simple (open or closed) and is the pullback of `A` along a
projection `proj` of plays, together
with maps lifting strategies of the auxiliary game to strategies of the original game in
such a way that every play against a lifted strategy is the projection of some play
against the original strategy.

Martin's unraveling theorem states that every Borel `A` admits such an unraveling; it is
the only ingredient of Martin's proof that is not formalized here. -/
structure Unraveling (A : Set (ℕ → X)) where
  /-- the move set of the auxiliary (covering) game -/
  Y : Type u
  [nonemptyY : Nonempty Y]
  /-- projection of plays of the covering game to plays of the original game -/
  proj : (ℕ → Y) → (ℕ → X)
  /-- the payoff set of the covering game -/
  payoff : Set (ℕ → Y)
  /-- the covering game has a topologically simple (open or closed, e.g. clopen) payoff -/
  simple_payoff : IsOpenPayoff payoff ∨ IsOpenPayoff payoffᶜ
  pullback : payoff = proj ⁻¹' A
  /-- lifting of player I's strategies -/
  liftI : Strategy Y → Strategy X
  /-- lifting of player II's strategies -/
  liftII : Strategy Y → Strategy X
  liftI_spec : ∀ (s : Strategy Y) (τ : Strategy X), ∃ t : Strategy Y,
    proj (playFrom [] s t) = playFrom [] (liftI s) τ
  liftII_spec : ∀ (t : Strategy Y) (σ : Strategy X), ∃ s : Strategy Y,
    proj (playFrom [] s t) = playFrom [] σ (liftII t)

attribute [instance] Unraveling.nonemptyY

/-- Any open payoff set is unraveled by itself (the identity covering); in particular
unravelings exist. -/
