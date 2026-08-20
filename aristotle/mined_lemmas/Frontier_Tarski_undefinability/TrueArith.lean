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

def TrueArith : Set ℕ :=
  {n | ∃ s : AFormula, IsSentence s ∧ encodeF s = n ∧ Sat s (fun _ => 0)}

/-- A set of natural numbers is arithmetically definable if it is the extension, in the
standard model, of an arithmetical formula in the single free variable `v 0`. -/
