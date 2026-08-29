/-
# Tarski Undefinability
Category: Frontier — Set Theory
Target: Frontier.Tarski_undefinability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

open FirstOrder Language

namespace Frontier

/-! ## The first-order language of arithmetic and its standard model

We work with the usual first-order language of arithmetic, with constants `0` and `1`,
binary function symbols `+` and `*`, and the binary relation symbol `≤`, interpreted in
the standard model `ℕ`.
-/

/-- Function symbols of the language of arithmetic: `0`, `1`, `+`, `*`. -/
inductive arithFunc : ℕ → Type
  | zero : arithFunc 0
  | one : arithFunc 0
  | add : arithFunc 2
  | mul : arithFunc 2
  deriving DecidableEq

/-- Relation symbols of the language of arithmetic: `≤`. -/
inductive arithRel : ℕ → Type
  | le : arithRel 2
  deriving DecidableEq

/-- The first-order language of arithmetic. -/

theorem Tarski_undefinability_of_encoding (code : arith.Formula (Fin 1) → ℕ) :
    ¬ ∃ θ : arith.Formula (Fin 2),
        ∀ (p : arith.Formula (Fin 1)) (n : ℕ),
          ((Sentence.Realize ℕ (θ.subst ![numeral (code p), numeral n] : arith.Sentence)) ↔
            p.Realize (M := ℕ) ![n]) := by
  rintro ⟨θ, hθ⟩
  refine Tarski_undefinability ⟨θ, fun p => ⟨code p, fun n => ?_⟩⟩
  have h := hθ p n
  have hv : ∀ w : Empty → ℕ,
      (fun a : Fin 2 => Term.realize (M := ℕ) w (![numeral (code p), numeral n] a)) =
        ![code p, n] := by
    intro w; funext i; fin_cases i <;> simp
  rw [Sentence.Realize, Formula.Realize, BoundedFormula.realize_subst, hv] at h
  exact h

/-- An explicit form of the diagonal argument: for every arithmetical formula `θ(x, y)` the
arithmetical formula `p(y) := ¬ θ(y, y)` is not among the "definable sets" enumerated by `θ`;
the index `e` itself always witnesses the failure. This shows the content of
`Frontier.Tarski_undefinability`: the missing set is itself arithmetically definable. -/
