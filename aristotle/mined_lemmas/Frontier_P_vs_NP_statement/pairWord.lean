import Mathlib

/-!
# P Vs NP Statement
Category: Frontier — Moonshot
Target: Frontier.P_vs_NP_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-! ## Words and tapes

Languages are sets of finite binary strings.  Machines work on a one-sided-infinite-free,
two-way infinite tape over the alphabet `Option Bool`, where `none` is the blank symbol.
We reuse Mathlib's `Turing.Tape` for the tape datatype. -/

/-- A binary word: the inputs of our machines. -/
abbrev Word : Type := List Bool

/-- The tape alphabet: `none` is the blank symbol, `some b` is the bit `b`. -/
abbrev Alph : Type := Option Bool

/-- The initial tape holding the input word `x`, with the head on its first cell. -/

def pairWord (x w : Word) : Word := (x.flatMap fun b => [true, b]) ++ [false, false] ++ w

/-- The *bit graph* of a function `f : Word → Word`: the language of all pairs `(x, 1 ^ i)`
such that the `i`-th bit of `f x` exists and equals `true`. -/
