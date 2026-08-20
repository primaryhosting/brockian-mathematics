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

theorem PAaxiom.holds {p : Formula} (h : PAaxiom p) (env : ℕ → ℕ) : p.holds env := by
  induction h with
  | taut ht => exact ht.holds env
  | instantiate p t =>
      intro h
      rw [Formula.holds_inst]
      exact h _
  | allImp p q =>
      intro h hp m
      exact h m (hp m)
  | vacuous p =>
      intro h m
      exact (Formula.holds_shift p m env).mpr h
  | eqRefl t => rfl
  | eqSubst p t u =>
      intro he h
      rw [Formula.holds_inst] at h ⊢
      rwa [← he]
  | succNeZero => intro m h; simp [Formula.holds, Term.eval] at h
  | succInj => intro m k h; simpa [Formula.holds, Term.eval] using h
  | addZero => intro m; rfl
  | addSucc => intro m k; rfl
  | mulZero => intro m; simp [Formula.holds, Term.eval]
  | mulSucc =>
      intro m k
      simp only [Formula.holds, Term.eval, cons]
      ring
  | induction p =>
      intro h0 hstep m
      induction m with
      | zero => exact (Formula.holds_inst p .zero env).mp h0
      | succ n ih =>
          have := hstep n ih
          exact (Formula.holds_instSucc p n env).mp this

/-- **Soundness**: everything provable in `PA` holds in the standard model. -/
