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

noncomputable def savDSM (M : NSM) (d : ℕ) : DSM where
  Cfg := SavCfg M d
  fintypeCfg := inferInstance
  start := (⟨[((some M.start, none, 0, 0) : Frame M)], by simp⟩, false)
  head := fun c => rawHead M c.1.val
  next := fun c t =>
    let r := rawStep M d (c.1.val, c.2) t
    if h : r.1.length ≤ d + 1 then (⟨r.1, h⟩, r.2) else c
  out := fun c => match c.1.val with | [] => some c.2 | _ => none
  out_sticky := by
    rintro ⟨⟨l, hl⟩, r⟩ t hout
    cases l with
    | cons f rest => simp at hout
    | nil => simp [rawStep]

