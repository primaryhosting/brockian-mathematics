/-!
# P Vs NP Statement
Category: Frontier — Moonshot
Target: Frontier.P_vs_NP_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Frontier

/-! ## Tape alphabet, configurations and machines -/

/-- The tape alphabet: `none` is the blank symbol, `some b` a bit. -/
abbrev Alpha := Option Bool

/-- A language: a set of finite bit strings, presented as a predicate. -/
abbrev Language := List Bool → Prop

/-- A configuration of a one-tape Turing machine with state space `Λ`:
the current state, the (two-way infinite) tape contents and the head position. -/
structure Cfg (Λ : Type) where
  state : Λ
  tape : Int → Alpha
  pos : Int

/-- A (in general nondeterministic) one-tape Turing machine with state space `Λ`.
`δ q a (q', a', d)` holds when, reading the symbol `a` in state `q`, the machine may move
to state `q'`, write `a'` and move right (`d = true`) or left (`d = false`).
A state/symbol pair with no transition is a halting situation. -/
structure NTM (Λ : Type) where
  /-- the initial state -/
  start : Λ
  /-- the accepting states -/
  accept : Λ → Prop
  /-- the transition relation -/
  δ : Λ → Alpha → (Λ × Alpha × Bool) → Prop

variable {Λ : Type}

/-- The machine is deterministic: at most one transition per (state, symbol) pair. -/

def Outputs (c : Cfg Λ) (y : List Bool) : Prop :=
  (∀ i : Nat, i < y.length → c.tape (i : Int) = y[i]?) ∧ c.tape (y.length : Int) = none

/-- `M` computes the string function `f` within the time bound `T`. -/
