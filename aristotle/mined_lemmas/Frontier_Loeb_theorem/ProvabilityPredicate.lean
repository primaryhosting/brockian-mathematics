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

theorem ProvabilityPredicate.nonempty : Nonempty ProvabilityPredicate := by
  have hb : ∀ p : Formula, PA ⊩ box (Formula.eq (.var 0) (.var 0)) p := by
    intro p
    exact .ax (.eqRefl _)
  refine ⟨{ pr := Formula.eq (.var 0) (.var 0), D1 := ?_, D2 := ?_, D3 := ?_,
            diagonal := ?_ }⟩
  · exact fun p _ => hb p
  · exact fun p q => imp_of_provable _ (imp_of_provable _ (hb q))
  · exact fun p => imp_of_provable _ (hb _)
  · refine fun p => ⟨p, ?_⟩
    refine mp_taut (p := box (Formula.eq (.var 0) (.var 0)) p) ?_ (hb p)
    intro v
    simp only [Formula.iff, Formula.and, Formula.pEval]
    cases Formula.pEval v (box (Formula.eq (Term.var 0) (Term.var 0)) p) <;>
      cases Formula.pEval v p <;> simp

/-- The Gödel numbering of terms is injective. -/
