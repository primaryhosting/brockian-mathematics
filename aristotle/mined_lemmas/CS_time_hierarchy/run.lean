/-!
# Time Hierarchy
Category: Frontier Cs
Target: CS.time_hierarchy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file is self-contained (no imports): a Lean module doc comment has to precede any
`import` command, and the required header above is a module doc comment, so the
development below is built from Lean core only.

We fix a small but genuine machine model: a step-indexed interpreter `run` for programs
coded by natural numbers, define the time-bounded classes `TIME t`, and prove by
diagonalization that allowing one extra step strictly increases the family of decidable
languages.
-/

namespace CS

/-- Inputs are pairs of natural numbers: the first component is read as (the code of) a
program, the second one as a clock. -/
abbrev Input : Type := Nat × Nat

/-- A *language* is a decidable predicate on inputs. -/
abbrev Lang : Type := Input → Bool

/--
`run s e x` runs the program with code `e` on input `x` for at most `s` steps.
It returns `some b` if the program halts within `s` steps with output `b`, and `none` if
it has not halted yet.

A program code `e : Nat` is decoded as an opcode `e % 3` together with an argument `e / 3`:

* opcode `0`: the constant program, outputting `true` iff its argument is `1`;
* opcode `1`: negation — run the subprogram whose code is the argument and flip the
  answer, at the cost of one extra step;
* opcode `2`: the *clocked diagonalizer* — on input `x = (a, k)` simulate the program with
  code `a` on the very same input `x` for `k + 1` steps and flip its answer, answering
  `true` if the simulated program has not halted in time.  The simulation is step for
  step, with one extra step of overhead.
-/

def run : Nat → Nat → Input → Option Bool
  | 0, _, _ => none
  | s + 1, e, x =>
    match e % 3 with
    | 0 => some (decide (e / 3 = 1))
    | 1 => (run s (e / 3) x).map (fun b => !b)
    | _ =>
        match run (min s (x.2 + 1)) x.1 x with
        | some b => some (!b)
        | none => if x.2 + 1 ≤ s then some true else none
  termination_by s => s
  decreasing_by
  · omega
  · omega

/-! ### Basic equations for the interpreter -/

