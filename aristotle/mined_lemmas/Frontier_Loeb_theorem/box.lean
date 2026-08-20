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

def box (pr : Formula) (p : Formula) : Formula := pr.inst (quote p)

/-- A **provability predicate** for `PA`: a formula `pr` with one free variable
satisfying the three Hilbert–Bernays–Löb derivability conditions, together with the
diagonal (fixed point) lemma for the box modality it defines.  These are the standard
properties of the arithmetized provability predicate of `PA`. -/
structure ProvabilityPredicate where
  /-- The formula `Pr(x)` expressing provability, with one free variable `x`. -/
  pr : Formula
  /-- **D1** (necessitation): if `PA ⊩ p` then `PA ⊩ □p`. -/
  D1 : ∀ p : Formula, (PA ⊩ p) → (PA ⊩ box pr p)
  /-- **D2** (distribution): `PA ⊩ □(p → q) → (□p → □q)`. -/
  D2 : ∀ p q : Formula, PA ⊩ (box pr (p ⟶ q) ⟶ (box pr p ⟶ box pr q))
  /-- **D3**: `PA ⊩ □p → □□p`. -/
  D3 : ∀ p : Formula, PA ⊩ (box pr p ⟶ box pr (box pr p))
  /-- The **diagonal lemma** for the box modality: for every formula `p` there is a
  sentence `q` with `PA ⊩ q ↔ (□q → p)`. -/
  diagonal : ∀ p : Formula, ∃ q : Formula, PA ⊩ Formula.iff q (box pr q ⟶ p)

/-! ## Propositional reasoning inside `PA` -/

