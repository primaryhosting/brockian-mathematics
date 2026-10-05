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
-/

/-!
## Overview

Hilbert's tenth problem asks for an algorithm which decides whether a polynomial equation
with integer coefficients has a solution in natural numbers.  We formalise instances of
the problem as pairs `(P, Q)` of polynomials with *natural* coefficients (an equation with
integer coefficients is turned into this shape by moving negative monomials to the other
side), encoded concretely as lists of monomials, so that instances form a `Primcodable`
type and "algorithm" can be taken to mean `Computable` in Mathlib's sense.

The main theorem `CS.hilbert10_undecidable` states that, granted the MRDP theorem — every
computably enumerable predicate on `ℕ` is Diophantine, phrased with Mathlib's own `Dioph`
predicate — solvability of such equations is not a computable predicate.  MRDP itself is
not available in Mathlib and is not proved here; it enters as an explicit hypothesis
`CS.Hilbert10.MRDP` of the main theorem (no axiom is added to the environment).

Everything else is proved unconditionally:

* `CS.Hilbert10.dioph_to_eqn` and `CS.Hilbert10.eqn_to_dioph`: Mathlib's `Dioph` predicate
  for sets of naturals matches parametric solvability of a concrete equation of the above
  shape; `CS.Hilbert10.mrdp_iff` records the resulting reformulation of MRDP.
* `CS.Hilbert10.solvable_re`: solvability is computably enumerable (the easy half of
  MRDP: one can search for a solution).
* `CS.Hilbert10.specialize` and `CS.Hilbert10.computable_specialize`: substituting a value
  for the parameter `x 0` is a primitive recursive operation on equations, and
  `CS.Hilbert10.solvable_specialize` shows it does what it should.
* `CS.Hilbert10.undecidable_of_dioph`: *any* undecidable Diophantine predicate on `ℕ`
  makes Hilbert's tenth problem undecidable; the main theorem instantiates this with the
  halting problem, so only Diophantineness of the halting set is actually used.
-/

namespace CS

namespace Hilbert10

/-- A monomial in variables indexed by `γ`: a natural number coefficient together with the
list of variable indices occurring in it (with multiplicity).  The monomial `(c, [i, j, i])`
denotes `c * x i * x j * x i`. -/
abbrev Mon (γ : Type*) := ℕ × List γ

/-- A polynomial with natural number coefficients in variables indexed by `γ`, represented
as a list of monomials (to be summed). -/
abbrev NPoly (γ : Type*) := List (Mon γ)

/-- An instance of Hilbert's tenth problem: a Diophantine equation `P = Q`, given by a pair
of polynomials with natural coefficients in the variables `x 0, x 1, …`.  Every polynomial
equation with integer coefficients can be put in this form by moving the negative monomials
to the other side. -/
abbrev Eqn := NPoly ℕ × NPoly ℕ

variable {γ δ : Type*}

/-- Value of a monomial at an assignment of natural numbers to the variables. -/

lemma eval_congr {p : NPoly γ} {x y : γ → ℕ} (h : ∀ j ∈ vars p, x j = y j) :
    eval p x = eval p y := by
  induction p with
  | nil => rfl
  | cons m p ih =>
      have hm : ∀ j ∈ m.2, x j = y j := fun j hj => h j (by simp [vars, hj])
      have hp : ∀ j ∈ vars p, x j = y j := fun j hj => by
        refine h j ?_
        simp only [vars, List.flatMap_cons, List.mem_append]
        exact Or.inr hj
      have : (m.2.map x) = (m.2.map y) := List.map_congr_left hm
      simp only [eval_cons, evalMon, this, ih hp]

/-- Every multivariate integer polynomial in Mathlib's sense is the difference of two
polynomials with natural coefficients. -/
