import Mathlib

/-!
# Gale Stewart Open
Category: Frontier — Set Theory
Target: Frontier.Gale_Stewart_open
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

variable {A : Type*}

/-- The list of the first `n` moves of the play `f`. -/

lemma playAux_length (σ τ : Strategy A) (n : ℕ) : (playAux σ τ n).length = n := by
  induction n with
  | zero => simp [playAux]
  | succ n ih => simp [playAux, ih]

/-- Any pair of strategies determines a play following both of them; in particular the two
disjuncts of the determinacy statement are not vacuous. -/
