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

lemma step_exhaust (c : SavCfg M d) (a b : Option M.Cfg) (i : Fin (NN M + 1))
    (rest : List (Frame M)) (hc : c.1.val = ((a, b, i, 0) : Frame M) :: rest)
    (hk : d + 1 - (rest.length + 1) ≠ 0) (hi : ¬ (i : ℕ) < NN M) :
    valOf ((savDSM M d).trans x c) = (rest, false) := by
  have hlen := stack_len hc
  have hk2 : ¬ (d - rest.length = 0) := by omega
  have hraw : rawStep M d (valOf c) (bitAt x (rawHead M c.1.val)) = (rest, false) := by
    simp [rawStep, valOf, hc, rawHead, hk2, hi]
  rw [sav_step x c (by rw [hraw]; simp only [List.length_cons]; omega)]
  exact hraw

