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

theorem quote_injective : Function.Injective quote := by
  intro p q h
  refine Formula.encode_injective ?_
  have : ∀ m n : ℕ, numeral m = numeral n → m = n := by
    intro m
    induction m with
    | zero => intro n hn; cases n with
      | zero => rfl
      | succ n => simp [numeral] at hn
    | succ m ih => intro n hn; cases n with
      | zero => simp [numeral] at hn
      | succ n => simp only [numeral, Term.succ.injEq] at hn; exact congrArg _ (ih n hn)
  exact this _ _ h

/-! ## Standard semantics: soundness and consistency of `PA`

The following section checks that the proof calculus above is not degenerate: it is sound
for the standard model `ℕ`, and in particular `PA ⊬ ⊥`.
-/

/-- Extending an environment by a value for the de Bruijn variable `0`. -/
