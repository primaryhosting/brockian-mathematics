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

lemma sav_step {M : NSM} {d : ℕ} (x : List Bool) (c : SavCfg M d)
    (h : (rawStep M d (valOf c) (bitAt x (rawHead M c.1.val))).1.length ≤ d + 1) :
    valOf ((savDSM M d).trans x c) = rawStep M d (valOf c) (bitAt x (rawHead M c.1.val)) := by
  simp only [DSM.trans, savDSM, valOf] at *
  rw [dif_pos h]

end Savitch

end CS

namespace CS

section SavitchSteps

variable {M : NSM} {d : ℕ} (x : List Bool)

