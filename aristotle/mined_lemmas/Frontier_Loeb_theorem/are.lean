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

/-!
# Löb's theorem

This file gives a self-contained formalization of the syntax of first-order arithmetic,
of the theory `PA` (Peano arithmetic) together with a Hilbert-style proof calculus, of
Gödel numbering of formulas, of the box modality `□φ = Pr(⌜φ⌝)` attached to a provability
predicate `Pr`, and a proof of **Löb's theorem**:

> if `PA ⊩ □φ → φ` then `PA ⊩ φ`.

Everything used in the statement is defined here from scratch: terms, formulas,
substitution, the axioms of `PA`, the provability relation `PA ⊩ ·`, the Gödel numbering
`⌜·⌝`, numerals and the box modality.

The three Hilbert–Bernays–Löb derivability conditions and the diagonal (fixed point)

lemma are *hypotheses* of the theorem, packaged in the structure
`Frontier.ProvabilityPredicate`.  These are exactly the properties of the standard
`Σ₁` provability predicate of `PA` whose verification is the (purely arithmetical)
arithmetization of syntax; they are not proved here.  Löb's theorem is precisely the
statement that they *imply* `PA ⊩ □φ → φ  ⟹  PA ⊢ φ`.

That the hypotheses are consistent (so that the theorem is not vacuous) is witnessed by
`Frontier.ProvabilityPredicate.nonempty`.  As sanity checks on the definitions we also
prove that the Gödel numbering is injective (`Frontier.quote_injective`) and that the
calculus is sound for the standard model (`Frontier.Provable.sound`), hence consistent
(`Frontier.PA_consistent`).
-/

namespace Frontier

/-! ## Syntax of first-order arithmetic -/

/-- Terms of the language of arithmetic `{0, S, +, ·}`.  Variables are de Bruijn indices. -/
inductive Term where
  | var : ℕ → Term
  | zero : Term
  | succ : Term → Term
  | add : Term → Term → Term
  | mul : Term → Term → Term
  deriving DecidableEq

/-- Formulas of the language of arithmetic, with primitive connectives `⊥`, `→` and `∀`
(de Bruijn style: `all p` binds the variable with index `0` in `p`). -/
inductive Formula where
  /-- An equation `t = u` between terms. -/
  | eq : Term → Term → Formula
  /-- Falsity. -/
  | bot : Formula
  /-- Implication. -/
  | imp : Formula → Formula → Formula
  /-- Universal quantification over the de Bruijn variable `0`. -/
  | all : Formula → Formula
  deriving DecidableEq

@[inherit_doc] infixr:26 " ⟶ " => Formula.imp

/-- Negation. -/
