/-
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace CS

/-! ## Machine model

We work with a *non-uniform* space-bounded machine model.  A machine works on inputs of one
fixed length; a language belongs to a space class if for every input length there is a machine
of the appropriate size deciding the language on inputs of that length.

A machine is described by its set of configurations `Cfg` (which is the whole memory of the
machine: the space used is `log₂ (card Cfg)`), a designated start configuration, a function
`head` telling which position of the (read-only) input is currently scanned, and a transition
which may depend on the current configuration and on the single input bit that is being read.
Note that the machine has *no* other access to the input, which is what makes the space measure
meaningful. -/

/-- The `i`-th bit of an input word; `false` beyond the end of the word. -/

lemma reachSet_stab {a : C} {t : ℕ} (h : reachSet E a t = reachSet E a (t + 1)) :
    ∀ u, reachSet E a (t + u) = reachSet E a t := by
  intro u
  induction u with
  | zero => rfl
  | succ u ih =>
      have : reachSet E a (t + u + 1) = stepSet E (reachSet E a (t + u)) := reachSet_succ a _
      rw [show t + (u + 1) = (t + u) + 1 from rfl, this, ih, ← reachSet_succ, ← h]

