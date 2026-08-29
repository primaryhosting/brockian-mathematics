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

@[simp] theorem Sat_ex (env : Nat → Nat) (p : AFormula) :
    Sat env (.ex p) ↔ ∃ n, Sat (cons n env) p := Iff.rfl

