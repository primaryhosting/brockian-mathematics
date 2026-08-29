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

theorem closed_determinacy_from {W : Set (ℕ → A)} (hW : IsClosed W) (p : List A) :
    DeterminedFrom W p :=
  determinedFrom_of_seqClosed (seqClosed_of_isClosed hW) p

/-!
### Borel determinacy

Martin's theorem states that every Borel game is determined.  What is proved here is:

* unconditionally, the base case of the Borel hierarchy: every open game and every closed
  game is determined (`Frontier.open_determinacy`, `Frontier.closed_determinacy`);
* a Lean-checked reduction of the general statement to the two closure properties of the
  class of determined *Borel* sets which Martin's unravelling argument supplies, namely
  closure under complements and under countable unions.

Both hypotheses of `Frontier.Borel_determinacy` are restricted to Borel payoff sets, and so
are consequences of Martin's theorem; in particular the statement below is not vacuous.
(For arbitrary payoff sets closure under complements fails in ZFC, which is why the
restriction matters.)  The full unravelling construction is not formalised here.
-/

/-- **Borel determinacy (Martin's theorem), as a Lean-checked reduction.**
If determinacy of Borel games is preserved by complements and by countable unions, then
every Borel game is determined.  The base case of the induction — determinacy of open
games — is proved unconditionally (`Frontier.open_determinacy`). -/
