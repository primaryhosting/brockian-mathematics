import Mathlib

/-!
# Cook Levin
Category: Frontier — Moonshot
Target: Frontier.cook_levin
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
## Overview

This file formalises the combinatorial core of the Cook–Levin theorem: *bounded
nondeterministic computation is reducible to Boolean satisfiability*.

The model of computation is a **sequential Boolean circuit machine**: a machine has a
configuration consisting of `width` bits, and one Boolean circuit (a straight-line
program of NAND gates, constants and reads of the current configuration) per output bit,
describing how the configuration is updated in one step.  Running the machine for `t`
steps from an initial configuration `c₀` and looking at the designated accepting bit
`acc` gives the acceptance predicate `Frontier.Accepts`.

Nondeterminism is the usual "guess" formulation: the input `x : List Bool` is written on
the first `x.length` bits of the initial configuration, and all remaining bits of the
initial configuration are unconstrained (they are the witness / nondeterministic guess).

The reduction `Frontier.tableau M x t` is the explicit computation tableau CNF:
a Boolean variable for every configuration bit at every time step, a Tseitin variable for
every gate of every step circuit at every time step, together with clauses forcing the
input bits, forcing the gate variables to compute the circuits, linking each layer to the
next, and asserting acceptance.

The main theorem `Frontier.cook_levin` says that `x` is accepted (for some witness) within
`t` steps **iff** the CNF `tableau M x t` is satisfiable, i.e. the explicit map
`x ↦ tableau M x (tb x.length)` is a many-one reduction of the language of `M` to `SAT`.
`Frontier.tableau_length_le` gives the accompanying size bound, which is polynomial
whenever the time bound, the width and the circuit sizes are polynomial; this is what
makes the reduction a polynomial-time (Karp) reduction.
-/

namespace Frontier

/-! ### CNF formulas -/

/-- An assignment of truth values to (natural-number indexed) Boolean variables. -/
abbrev Assign := ℕ → Bool

/-- A literal: a variable index together with the polarity that makes it true. -/
abbrev Lit := ℕ × Bool

/-- A clause is a disjunction of literals. -/
abbrev Clause := List Lit

/-- A CNF formula is a conjunction of clauses. -/
abbrev CNFFormula := List Clause

/-- A clause is satisfied by `σ` when one of its literals is true under `σ`. -/

private def c₀of (σ : Assign) : Assign := fun p => σ (vCfg 0 p)

