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

lemma valOf_snd {c : SavCfg M d} {L : List (Frame M)} {v : Bool} (h : valOf c = (L, v)) :
    c.2 = v := congrArg Prod.snd h

/-- Correctness of a recursive call of the Savitch machine: started on a frame `(a, b, 0, 0)`
at recursion level `k`, the machine eventually pops that frame, returning `RkB _ k a b`. -/
