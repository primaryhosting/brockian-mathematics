/-!
# Time Hierarchy
Category: Frontier Cs
Target: CS.time_hierarchy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

This file is self-contained: it depends on nothing but the Lean core library.

We set up a concrete model of computation.  Inputs are natural numbers, programs are
natural numbers as well (a code is read as `pair tag args`, so that every natural number
is a program), and `eval k c x` runs the program `c` on input `x` with a budget of `k`
steps.  The instruction set contains the basic arithmetic and pairing operations, a
conditional, an unbounded loop, and one universal instruction which runs a given program
on a given input under a given step budget, at the cost of that budget plus one step.

`InTime t L` says that the language `L : Nat → Bool` is decided by some program within
`t x` steps on every input `x`.  Since running a program with more fuel gives the same
result (`eval_mono`), these classes grow with `t`.

The main result `CS.time_hierarchy` is the time hierarchy theorem for this model: if the
time bound `t` is itself computable within time `b`, and `T x ≥ t x + b x + 8`, then
every language decidable in time `t` is decidable in time `T`, and some language --
the diagonal language `diagLang t` -- is decidable in time `T` but not in time `t`.
-/

namespace CS

/-! ## A pairing function on `Nat` -/

/-- `twos d` is the 2-adic valuation of `d` (with `twos 0 = 0`). -/

def encOpt : Option Nat → Nat
  | none => 0
  | some v => v + 1

/--
`eval k c x` runs the program with code `c` on input `x` with a budget (fuel) of `k`
steps, returning `some v` if it produces the output `v` within the budget and `none`
otherwise.

A code `c` is read as `pair tag args`; the tag selects the instruction:

* `0`: identity
* `1`: the constant `args`
* `2`: successor
* `3`: predecessor
* `4`: pairing of the two subprograms in `args`
* `5`, `6`: the two projections
* `7`: composition of the two subprograms in `args`
* `8`: `if f x = 0 then g x else h x`
* `9`: the loop `x ↦ if x = 0 then 0 else loop f (f x)` (unbounded recursion)
* `10`: the universal instruction: on input `pair k' (pair c' x')` it runs the program
  `c'` on the input `x'` with a budget of `k'` steps, and reports the (encoded) result.
  It requires a budget of at least `k' + 1` steps.

Every instruction consumes one unit of fuel, and subprograms are run with the
remaining fuel.
-/
