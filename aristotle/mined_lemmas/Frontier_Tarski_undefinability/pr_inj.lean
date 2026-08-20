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
# Tarski's undefinability of truth

We formalize, from scratch, the statement that arithmetical truth is not arithmetically
definable.

* `Frontier.ATerm` / `Frontier.AFormula` : the syntax of first-order arithmetic
  (variables indexed by `ℕ`, a constant for each natural number, `+`, `*`, `=`, `¬`, `∧`, `∃`).
* `Frontier.Sat` : satisfaction in the standard model `ℕ`.
* `Frontier.IsSentence` : having no free variables.
* `Frontier.encodeF` : an injective Gödel numbering of formulas (`Frontier.encodeF_inj`).
* `Frontier.TrueArith` : the set of Gödel numbers of true arithmetical sentences.
* `Frontier.ArithDefinable` : a set of naturals is definable by an arithmetical formula.
* `Frontier.no_truth_predicate` : no formula satisfies the Tarski biconditionals.
* `Frontier.Tarski_undefinability` : `¬ ArithDefinable TrueArith`.

The key step is the diagonal construction: for a formula `p` with a single free variable,
the sentence `sub1 p m` is `∃ v₀, v₀ = m ∧ p`, which says that `p` holds of `m`. Because the
Gödel numbering is built from the polynomial pairing function `Frontier.pr`, the code of
`sub1 p m` is a *polynomial* in the code of `p` and in `m` (`Frontier.encodeF_sub1`), so the
diagonal function `a ↦ encodeF (sub1 p a)` (for `a = encodeF p`) is computed by an explicit
term `Frontier.diagTerm` of the language itself. No further arithmetization is needed.

The last section (`Frontier.ArithDefinable_pure`) shows that the constants for all natural
numbers are eliminable: every definable set is defined by a formula whose only constants are
`0` and `1`, i.e. a formula of the usual language `{0, 1, +, ·}` of arithmetic.
-/

namespace Frontier

/-! ## A polynomial pairing function -/

/-- An injective polynomial pairing function on `ℕ`. -/

theorem pr_inj {a b c d : ℕ} (h : pr a b = pr c d) : a = c ∧ b = d := by
  have key : a + b = c + d := by
    rcases lt_trichotomy (a + b) (c + d) with hlt | he | hgt
    · exfalso
      have h1 : a + b + 1 ≤ c + d := hlt
      have h2 : (a + b + 1) * (a + b + 1) ≤ (c + d) * (c + d) := Nat.mul_le_mul h1 h1
      have h3 : a ≤ a + b := Nat.le_add_right a b
      simp only [pr] at h
      nlinarith
    · exact he
    · exfalso
      have h1 : c + d + 1 ≤ a + b := hgt
      have h2 : (c + d + 1) * (c + d + 1) ≤ (a + b) * (a + b) := Nat.mul_le_mul h1 h1
      have h3 : c ≤ c + d := Nat.le_add_right c d
      simp only [pr] at h
      nlinarith
  have ha : a = c := by
    simp only [pr, key] at h
    exact Nat.add_left_cancel h
  exact ⟨ha, by omega⟩

/-! ## Syntax -/

/-- Terms of the language of arithmetic: variables `v i` (`i : ℕ`), a constant for every
natural number, addition and multiplication. -/
inductive ATerm : Type
  | var : ℕ → ATerm
  | num : ℕ → ATerm
  | add : ATerm → ATerm → ATerm
  | mul : ATerm → ATerm → ATerm
  deriving DecidableEq

/-- Formulas of the language of arithmetic: equations between terms, negation, conjunction
and existential quantification. -/
inductive AFormula : Type
  | eqf : ATerm → ATerm → AFormula
  | neg : AFormula → AFormula
  | conj : AFormula → AFormula → AFormula
  | ex : ℕ → AFormula → AFormula
  deriving DecidableEq

/-! ## Semantics in the standard model `ℕ` -/

/-- Value of a term under an assignment of natural numbers to the variables. -/
