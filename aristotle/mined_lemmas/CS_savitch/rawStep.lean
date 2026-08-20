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

noncomputable def rawStep (M : NSM) (d : ℕ) (c : List (Frame M) × Bool) (t : Bool) : List (Frame M) × Bool :=
  match c.1 with
  | [] => c
  | (a, b, i, ph) :: rest =>
      if d + 1 - (rest.length + 1) = 0 then (rest, decide (a = b) || M.edge' a t b)
      else if (ph : ℕ) = 0 then
        (if (i : ℕ) < NN M then
            (((a, cand M (i : ℕ), 0, 0) : Frame M) :: ((a, b, i, 1) : Frame M) :: rest, c.2)
          else (rest, false))
      else if (ph : ℕ) = 1 then
        (if c.2 = true then
            (((cand M (i : ℕ), b, 0, 0) : Frame M) :: ((a, b, i, 2) : Frame M) :: rest, c.2)
          else (((a, b, incF M i, 0) : Frame M) :: rest, false))
      else
        (if c.2 = true then (rest, true)
          else (((a, b, incF M i, 0) : Frame M) :: rest, false))

/-- The input position scanned in a raw configuration. -/
