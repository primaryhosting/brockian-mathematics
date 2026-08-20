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

theorem loeb_chain {a c d e f : Formula}
    (h1 : PA ⊩ (a ⟶ c)) (h2 : PA ⊩ (c ⟶ (d ⟶ e))) (h3 : PA ⊩ (a ⟶ d))
    (h4 : PA ⊩ (e ⟶ f)) : PA ⊩ (a ⟶ f) := by
  have key : Tautology ((a ⟶ c) ⟶ ((c ⟶ (d ⟶ e)) ⟶ ((a ⟶ d) ⟶ ((e ⟶ f) ⟶ (a ⟶ f))))) := by
    intro v
    simp only [Formula.pEval]
    cases Formula.pEval v a <;> cases Formula.pEval v c <;> cases Formula.pEval v d <;>
      cases Formula.pEval v e <;> cases Formula.pEval v f <;> simp
  exact .mp (.mp (.mp (.mp (provable_of_tautology key) h1) h2) h3) h4

/-! ## Löb's theorem -/

/-- **Löb's theorem**.  Let `Pr` be a provability predicate for Peano arithmetic, i.e. a
formula satisfying the Hilbert–Bernays–Löb derivability conditions and the diagonal
lemma, and write `□a` for `Pr(⌜a⌝)`.  If `PA ⊩ □a → a`, then `PA ⊩ a`. -/
