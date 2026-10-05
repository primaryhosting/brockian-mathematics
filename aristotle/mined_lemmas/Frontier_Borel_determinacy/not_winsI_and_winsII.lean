import Mathlib
/-!
# Borel Determinacy
Category: Frontier — Set Theory
Target: Frontier.Borel_determinacy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000
set_option autoImplicit false

/-!
## Infinite two-player games of perfect information

We work with the Gale–Stewart game on a nonempty type `A`:  players I and II alternately
choose elements of `A`, player I moving first, producing an infinite play `x : ℕ → A`.
Player I wins the play iff `x ∈ W`.
-/

namespace Frontier

variable {A : Type*}

/-- The list of the first `n` moves of the play `x`. -/

theorem not_winsI_and_winsII (W : Set (ℕ → A)) (σ τ : List A → A) :
    ¬ (WinsI W σ ∧ WinsII W τ) := by
  rintro ⟨h1, h2⟩
  exact h2 (playSeq σ τ) (playII_playSeq σ τ) (h1 (playSeq σ τ) (playI_playSeq σ τ))

/-!
### The reachability game

`Force T S p` says that the player whose turn positions are given by `T` can force,
from the position `p`, that the play visits a position in `S`.  It is defined as the
least such predicate, i.e. by an inductive definition.
-/

/-- The player with turn set `T` can force the play to reach a position in `S`. -/
inductive Force (T : List A → Prop) (S : List A → Prop) : List A → Prop
  | here {p : List A} (h : S p) : Force T S p
  | reach {p : List A} (hp : T p) (a : A) (h : Force T S (p ++ [a])) : Force T S p
  | opp {p : List A} (hp : ¬ T p) (h : ∀ a : A, Force T S (p ++ [a])) : Force T S p

variable [Nonempty A]

/-- If the `T`-player can force reaching `S` from `p`, then it has a strategy doing so. -/
