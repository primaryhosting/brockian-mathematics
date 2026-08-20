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

lemma sav_outputs (M : NSM) (d : ℕ) (x : List Bool) :
    (savDSM M d).Outputs x (RkB (M.E' x) d (some M.start) none) := by
  obtain ⟨t, ht⟩ := sav_call x d (some M.start) none [] (savDSM M d).start rfl (by simp)
  refine ⟨t, ?_⟩
  have h1 : (((savDSM M d).trans x)^[t] (savDSM M d).start).1.val = [] := valOf_fst ht
  have h2 : (((savDSM M d).trans x)^[t] (savDSM M d).start).2
      = RkB (M.E' x) d (some M.start) none := valOf_snd ht
  rw [DSM.run, savDSM_out, h1, ← h2]

