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

def bitAt (x : List Bool) (i : ℕ) : Bool := x.getD i false

/-- A nondeterministic machine with configuration set `Cfg`. -/
structure NSM where
  /-- The set of configurations (the entire memory of the machine). -/
  Cfg : Type
  /-- The configuration set is finite. -/
  fintypeCfg : Fintype Cfg
  /-- Configurations can be compared. -/
  decEqCfg : DecidableEq Cfg
  /-- The initial configuration. -/
  start : Cfg
  /-- The accepting configurations. -/
  acc : Cfg → Bool
  /-- Position of the input head in a given configuration. -/
  head : Cfg → ℕ
  /-- `step a t b` says that `b` is a legal successor of `a` when the scanned input bit is `t`. -/
  step : Cfg → Bool → Cfg → Bool

attribute [instance] NSM.fintypeCfg NSM.decEqCfg

/-- The configuration graph of a nondeterministic machine on the input `x`. -/
