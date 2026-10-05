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

open scoped Classical

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace CS

universe u

local infixr:65 " ⊗ " => Sum.elim

/-! ## Exponential polynomials

An *exponential polynomial* in variables of type `α` is built from variables and natural
number constants using addition, multiplication and exponentiation.  These are the objects
occurring in the Davis–Putnam–Robinson theorem. -/

/-- Syntax of exponential polynomials with variables in `α`. -/
inductive ExpPoly (α : Type u) : Type u
  | var : α → ExpPoly α
  | const : ℕ → ExpPoly α
  | add : ExpPoly α → ExpPoly α → ExpPoly α
  | mul : ExpPoly α → ExpPoly α → ExpPoly α
  | pow : ExpPoly α → ExpPoly α → ExpPoly α

/-- Evaluation of an exponential polynomial at a valuation `v : α → ℕ`. -/

theorem not_computablePred_haltsAt : ¬ ComputablePred haltsAt := by
  intro h
  obtain ⟨f, hf, hEq⟩ := ComputablePred.computable_iff.1 h
  refine ComputablePred.halting_problem 0 (ComputablePred.computable_iff.2
    ⟨fun c => f (Encodable.encode c), hf.comp Computable.encode, funext fun c => ?_⟩)
  have := congrFun hEq (Encodable.encode c)
  simpa [haltsAt, Denumerable.ofNat_encode] using this

/-- **Hilbert's tenth problem is undecidable** (the MRDP theorem, modulo the
Davis–Putnam–Robinson arithmetisation of recursively enumerable sets).

There is a single polynomial `p` with integer coefficients, in one distinguished parameter
`a` and finitely many further unknowns `t`, such that no algorithm decides, given `a`,
whether the Diophantine equation `p (a, t) = 0` has a solution `t` in the natural numbers.
In particular there is no algorithm solving Hilbert's tenth problem in general. -/
