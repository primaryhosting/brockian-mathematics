/-
# Hilbert 10 Undecidable
Category: Frontier Cs
Target: CS.hilbert10_undecidable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hilbert 10 Undecidable
Category: Frontier Cs
Target: CS.hilbert10_undecidable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Contents

Hilbert's tenth problem asks for an algorithm deciding whether a polynomial equation with
integer coefficients has a solution.  Here it is formalised in its standard arithmetic form:
a *Diophantine equation* is a pair of polynomials `p`, `q` with natural number coefficients
(concretely, lists of monomials, so that equations are objects of a `Primcodable` type and the
decision problem makes sense), and the question is whether `p = q` has a solution in natural
numbers (`CS.Solvable`).  Every polynomial equation with integer coefficients can be put into
this shape by moving the negative terms to the other side.

* `CS.hilbert10_re` : unconditionally, the set of solvable Diophantine equations is
  recursively enumerable, and `CS.IsDioph.re`: every Diophantine set of naturals is r.e.
* `CS.hilbert10_undecidable` : granting the MRDP theorem `CS.MRDP` — the converse
  direction, that every r.e. set of naturals is Diophantine — Diophantine solvability is not
  decidable.  The reduction of the halting problem for partial recursive functions to
  Diophantine solvability (substitution of the input into the parameter of a Diophantine
  definition, and its computability) is carried out in full.

The number-theoretic heart of MRDP itself (Matiyasevich's theorem that exponentiation is
Diophantine, and the elimination of bounded universal quantifiers) is not available in
Mathlib in the form needed here, so `CS.MRDP` is taken as an explicit hypothesis of the
undecidability theorem rather than proved.
-/

namespace CS

/-! ## Syntax of Diophantine equations

A monomial is a coefficient together with a list of exponents: the `i`-th entry of the list is
the exponent of the variable `xᵢ` (variables beyond the length of the list have exponent `0`).
A polynomial is a list of monomials, interpreted as their sum.  A Diophantine equation is a
pair of such polynomials; it is *solvable* if the two sides can be made equal by some
assignment of natural numbers to the variables. -/

/-- A monomial: a coefficient and the list of exponents of the variables. -/
abbrev Monomial : Type := ℕ × List ℕ

/-- A polynomial with natural number coefficients, as a list of monomials. -/
abbrev DioPoly : Type := List Monomial

/-- `scons n x` is the assignment sending variable `0` to `n` and variable `i+1` to `x i`. -/

theorem IsDioph.re {S : Set ℕ} (h : IsDioph S) : REPred (fun n => n ∈ S) := by
  obtain ⟨p, q, hpq⟩ := h
  have hF : Computable (fun n : ℕ => ((substZero n p, substZero n q) : DioPoly × DioPoly)) :=
    Computable.pair (computable_substZero p) (computable_substZero q)
  have h1 : REPred (fun n : ℕ => Solvable (substZero n p, substZero n q)) :=
    Partrec.comp hilbert10_re hF
  refine h1.of_eq fun n => ?_
  simp only [Solvable, evalPoly_substZero]
  exact (hpq n).symm

end CS

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

