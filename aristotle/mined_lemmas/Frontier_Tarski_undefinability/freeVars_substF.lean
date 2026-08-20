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

theorem freeVars_substF (k : ℕ) (s : ATerm) : ∀ p : AFormula,
    freeVars (substF k s p) ⊆ (freeVars p).erase k ∪ varsT s := by
  intro p
  induction p with
  | eqf t u =>
      simp only [substF, freeVars]
      intro j hj
      simp only [Finset.mem_union] at hj
      rcases hj with hj | hj
      · have := varsT_substT k s t hj
        simp only [Finset.mem_union, Finset.mem_erase] at this ⊢
        tauto
      · have := varsT_substT k s u hj
        simp only [Finset.mem_union, Finset.mem_erase] at this ⊢
        tauto
  | neg p ih => simpa [substF, freeVars] using ih
  | conj p q ihp ihq =>
      simp only [substF, freeVars]
      intro j hj
      simp only [Finset.mem_union] at hj
      rcases hj with hj | hj
      · have := ihp hj
        simp only [Finset.mem_union, Finset.mem_erase] at this ⊢
        tauto
      · have := ihq hj
        simp only [Finset.mem_union, Finset.mem_erase] at this ⊢
        tauto
  | ex i p ih =>
      by_cases hik : i = k
      · subst hik
        have hid : substF i s (AFormula.ex i p) = AFormula.ex i p := by simp [substF]
        rw [hid]
        intro j hj
        simp only [freeVars, Finset.mem_erase] at hj
        simp only [freeVars, Finset.mem_union, Finset.mem_erase]
        exact Or.inl ⟨hj.1, hj.1, hj.2⟩
      · simp only [substF, if_neg hik, freeVars]
        intro j hj
        simp only [Finset.mem_erase] at hj
        have := ih hj.2
        simp only [Finset.mem_union, Finset.mem_erase] at this ⊢
        rcases this with h | h
        · exact Or.inl ⟨h.1, hj.1, h.2⟩
        · exact Or.inr h

/-! ## The diagonal construction -/

/-- `sub1 p m` is the formula `∃ v₀, v₀ = m ∧ p`, i.e. `p` with the numeral `m` plugged into
its free variable `v 0`. -/
