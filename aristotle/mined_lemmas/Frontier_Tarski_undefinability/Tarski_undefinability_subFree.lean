/-!
# Tarski Undefinability
Category: Frontier — Set Theory
Target: Frontier.Tarski_undefinability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file is deliberately self-contained: it uses no imports at all (only Lean 4 core),
so that the required header comment can literally be the first thing in the file
(Lean forbids `import` after a module docstring).

Contents:

* `Frontier.ATerm`, `Frontier.AFormula` : syntax of first-order arithmetic (de Bruijn variables).
* `Frontier.tval`, `Frontier.Sat`       : Tarskian semantics in the standard model `Nat`.
* `Frontier.enc`                        : a Gödel numbering of formulas.
* `Frontier.Defines`, `Frontier.Arithmetical` : arithmetical definability of a set of naturals.
* `Frontier.TrueSentences`              : arithmetical truth, i.e. the set of Gödel numbers of
                                          true sentences of arithmetic.
* `Frontier.Tarski_undefinability`      : arithmetical truth is not arithmetically definable.
* `Frontier.exists_subFree_equiv`       : the primitive substitution constructor of the syntax
                                          is eliminable, so the formulas above express exactly
                                          the conditions expressible in the ordinary language
                                          of arithmetic.
* `Frontier.Tarski_undefinability_subFree` : the same undefinability statement, restricted to
                                          formulas of that ordinary language.
-/

set_option autoImplicit false

namespace Frontier

/-! ## Syntax of the language of arithmetic

Variables are de Bruijn indices (natural numbers); an assignment is a function `Nat → Nat`. -/

/-- Terms of the language of arithmetic: variables, numerals, addition, multiplication. -/
inductive ATerm : Type
  | var : Nat → ATerm
  | num : Nat → ATerm
  | add : ATerm → ATerm → ATerm
  | mul : ATerm → ATerm → ATerm
  deriving DecidableEq

/-- Formulas of the language of arithmetic.

Besides the usual clauses (equations, negation, conjunction, existential quantification over
the variable with de Bruijn index `0`), the syntax has a primitive *substitution* constructor
`sub p t`, whose semantics (see `Sat`) is the usual semantics of the substituted formula
`p[t/x₀]`.  Making substitution a syntactic primitive rather than a defined operation on syntax
trees does not change which truth conditions are expressible, but it allows a Gödel numbering
for which substitution of a numeral acts on codes by an explicit polynomial; this is what
replaces the usual arithmetization of syntax. -/
inductive AFormula : Type
  | eq : ATerm → ATerm → AFormula
  | not : AFormula → AFormula
  | and : AFormula → AFormula → AFormula
  | ex : AFormula → AFormula
  | sub : AFormula → ATerm → AFormula
  deriving DecidableEq

/-- Extend an assignment by a value for the variable with de Bruijn index `0`. -/

theorem Tarski_undefinability_subFree :
    ¬ ∃ θ : AFormula, SubFree θ ∧ Defines θ TrueSentences := by
  intro h
  obtain ⟨θ, _, hθ⟩ := h
  exact Tarski_undefinability ⟨θ, hθ⟩

end Frontier

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

