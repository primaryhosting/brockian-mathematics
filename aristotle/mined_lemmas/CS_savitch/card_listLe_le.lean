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

lemma card_listLe_le :
    Fintype.card {l : List α // l.length ≤ n} ≤ (Fintype.card α + 1) ^ n := by
  have h := Fintype.card_le_of_injective _ (listLeEnc_injective (α := α) n)
  simpa using h

end BoundedLists

end CS

namespace CS

/-! ## The deterministic Savitch machine

The deterministic machine implements the usual recursive procedure
`R k a b = ∃ m, R (k-1) a m ∧ R (k-1) m b` by an explicit stack of at most `d + 1` frames.
Each frame stores the two endpoints of the call, the index of the midpoint candidate currently
being tried, and a phase (0: start the first recursive call, 1: first call has returned,
2: second call has returned).  The recursion depth of a frame is determined by its position in
the stack, so it need not be stored. -/

section Savitch

/-- The number of configurations of the extended machine. -/
