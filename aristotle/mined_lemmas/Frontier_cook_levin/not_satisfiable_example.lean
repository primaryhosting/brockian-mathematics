import RequestProject.Frontier.Basic
import RequestProject.Frontier.Tableau
import RequestProject.Frontier.Correctness
import RequestProject.Frontier.Size
import RequestProject.Frontier.NP

import Mathlib

/-!
# The Cook–Levin theorem (tableau reduction)

This file develops, from scratch, the core of the Cook–Levin theorem: the *tableau
reduction* from an arbitrary nondeterministic Turing machine computation to the
satisfiability of a CNF formula.

## Main results

* `Frontier.tableau_satisfiable_iff`: for a well-formed nondeterministic Turing machine
  `M` with a tape of `N` cells, a time bound `T` and an input tape `x`, the explicitly
  constructed CNF formula `Frontier.tableau M N T x` is satisfiable if and only if `M`
  has an accepting computation on `x` of length `T`.
* `Frontier.tableau_length_le`: the tableau has polynomially many clauses.
* `Frontier.cook_levin`: **SAT is NP-hard**.  Every language in `Frontier.InNP` (defined
  via nondeterministic Turing machines with a polynomially bounded running time) is
  many-one reducible to satisfiability of CNF formulas, by the explicit reduction
  `Frontier.satReduction`, whose output has polynomially bounded size.
* `Frontier.satisfiable_iff_exists_certificate`: the membership half, at the level of
  certificates — a formula is satisfiable exactly when it admits a certificate of
  length `maxVar φ + 1` accepted by the explicit checker `Frontier.checkSat`.

## Scope

The hardness half is proved in full, including the polynomial bound on the size of the
produced formula; the reduction itself is an explicit, executable function.  What is
*not* formalised here is a machine-level cost model for computing the reduction, nor a
Turing machine implementation of a SAT verifier; the membership half is formalised in
the certificate form described above rather than by exhibiting such a machine.
-/

import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

import RequestProject.Frontier.Size

/-!
# SAT is NP-hard

Polynomially bounded functions, the class NP defined via nondeterministic Turing
machines, the Cook-Levin reduction, and the certificate characterisation of
satisfiability.
-/

namespace Frontier

/-! ## SAT is NP-hard

We now package the tableau reduction as the statement that SAT is NP-hard.
A language over the binary alphabet is in NP when it is decided by a
nondeterministic Turing machine within a polynomially bounded number of steps. -/

/-- `f` is bounded by a polynomial. -/

theorem not_satisfiable_example : ¬ Satisfiable [[⟨0, true⟩], [⟨0, false⟩]] := by
  rintro ⟨σ, hσ⟩
  cases hv : σ 0 <;> simp [cnfEval, clauseEval, litEval, hv] at hσ

/-- The CNF formula `x₀` is satisfiable. -/
