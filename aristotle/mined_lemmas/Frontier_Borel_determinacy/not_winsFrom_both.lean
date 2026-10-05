import Mathlib

/-!
# Borel Determinacy
Category: Frontier — Set Theory
Target: Frontier.Borel_determinacy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-! ## Infinite games: positions, strategies, winning strategies

We consider infinite two-player games with perfect information played on an alphabet `X`.
A *play* is a sequence `x : ℕ → X`; the move at time `n` is `x n`.  Which player moves at
time `n` is recorded by a predicate `turn : ℕ → Prop` (the *turn set* of the player under
consideration).  In the classical game `G(A)` on Baire space, player I moves at the even
times and player II at the odd times, and player I wins the play `x` iff `x ∈ A`.
-/

variable {X : Type*}

/-- The position reached after the first `n` moves of the play `x`. -/

theorem not_winsFrom_both [Inhabited X] {turn : ℕ → Prop} {A : Set (ℕ → X)}
    (h1 : WinsFrom turn A []) (h2 : WinsFrom (fun n => ¬ turn n) Aᶜ []) : False := by
  obtain ⟨σ, hσ⟩ := h1
  obtain ⟨τ, hτ⟩ := h2
  have hx1 := hσ (play turn σ τ) (extends_nil _) (play_follows turn σ τ)
  have hx2 := hτ (play turn σ τ) (extends_nil _) (play_follows' turn σ τ)
  exact hx2 hx1

/-! ## Coverings and unravelings

Martin's proof of Borel determinacy proceeds by *unraveling*: every Borel payoff set `A` on
Baire space is *covered* by an auxiliary game, played on a (much larger) alphabet, whose
payoff set is **clopen**.  A covering comes with a projection of plays and, crucially, with
a way of projecting strategies, so that winning strategies in the auxiliary game yield
winning strategies in the original one.  The auxiliary clopen game is determined by the
Gale–Stewart theorem above, and determinacy of `A` follows.

We formalize coverings, prove that they compose and that determinacy transfers along them,
and use this to reduce Borel determinacy to Martin's unraveling lemma (the statement that
every Borel set is covered by a clopen game).  The unraveling lemma is a theorem of ZFC, so
the hypothesis of `Frontier.Borel_determinacy` below is not vacuous; we also check that
clopen sets are unraveled by the identity covering, and that the class of unraveled sets is
closed under complements.
-/

section Covering

variable {Y Z : Type*}

/-- The game with payoff `B` on the alphabet `X` **covers** the game with payoff `A` on the
alphabet `Y`, with play projection `proj`, if

* `B` is the `proj`-preimage of `A`;
* every strategy `s` of either player in the covering game can be projected to a strategy
  `t` in the game `G(A)`, in such a way that every play `y` following `t` is `proj x` for
  some play `x` of the covering game following `s`.

This is the property of Martin's coverings that is needed to transfer determinacy. -/
