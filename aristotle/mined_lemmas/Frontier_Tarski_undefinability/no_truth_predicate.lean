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

theorem no_truth_predicate :
    ¬ ∃ T : AFormula, freeVars T ⊆ {0} ∧
      ∀ s : AFormula, IsSentence s → (Sat T (fun _ => encodeF s) ↔ Sat s (fun _ => 0)) := by
  rintro ⟨T, hT0, hT⟩
  -- the diagonal formula `dg(v₀) := ¬ T(diagTerm(v₀))`
  let dg : AFormula := .neg (substF 0 diagTerm T)
  have hdgfree : freeVars dg ⊆ {0} := by
    have h1 : freeVars dg ⊆ (freeVars T).erase 0 ∪ varsT diagTerm :=
      freeVars_substF 0 diagTerm T
    refine h1.trans ?_
    intro j hj
    simp only [Finset.mem_union, Finset.mem_erase] at hj
    rcases hj with ⟨hj0, hjT⟩ | hj
    · have hj1 : j ∈ ({0} : Finset ℕ) := hT0 hjT
      simp only [Finset.mem_singleton] at hj1
      exact absurd hj1 hj0
    · exact varsT_diagTerm hj
  set p : ℕ := encodeF dg with hp
  let sn : AFormula := sub1 dg p
  have hsent : IsSentence sn := isSentence_sub1 hdgfree p
  have hcode : encodeF sn = G p p := encodeF_sub1 dg p
  have hsat : ∀ v : ℕ → ℕ, Sat sn v ↔ ¬ Sat T (fun _ => G p p) := by
    intro v
    show Sat (sub1 dg p) v ↔ _
    rw [sat_sub1]
    have h1 : Sat dg (Function.update v 0 p) ↔
        ¬ Sat T (Function.update (Function.update v 0 p) 0
          (evalT diagTerm (Function.update v 0 p))) := by
      show (¬ Sat (substF 0 diagTerm T) (Function.update v 0 p)) ↔ _
      rw [Sat_substF 0 diagTerm varsT_diagTerm]
    rw [h1, evalT_diagTerm]
    simp only [Function.update_self, Function.update_idem]
    have h2 : Sat T (Function.update v 0 (G p p)) ↔ Sat T (fun _ => G p p) := by
      refine Sat_congr T ?_
      intro i hi
      have : i = 0 := by simpa using hT0 hi
      subst this
      simp
    rw [h2]
  have h1 : Sat sn (fun _ => 0) ↔ ¬ Sat T (fun _ => encodeF sn) := by
    rw [hcode]; exact hsat _
  have h2 : Sat T (fun _ => encodeF sn) ↔ Sat sn (fun _ => 0) := hT sn hsent
  tauto

/-- **Tarski's undefinability of truth**: the set of Gödel numbers of true sentences of
arithmetic is not definable by any formula of arithmetic (interpreted in the standard
model `ℕ`). -/
