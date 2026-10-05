import Mathlib

/-!
# Deutsch Jozsa
Category: Frontier Qi
Target: QI.deutsch_jozsa
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace QI

/-! ## Setup

We model the Deutsch–Jozsa algorithm on `n` query bits.  A computational basis
state is an element of `Fin n → Bool`, and a (pure) state of the query register
is a function `(Fin n → Bool) → ℂ` of amplitudes. -/

variable {n : ℕ}

/-- The sign `(-1)^b` attached to a Boolean value. -/

theorem card_true_of_constant (f : (Fin n → Bool) → Bool) (hf : IsConstant f) :
    (Finset.univ.filter (fun x : Fin n → Bool => f x = true)).card = 0 ∨
    (Finset.univ.filter (fun x : Fin n → Bool => f x = true)).card = 2 ^ n := by
  by_cases h : f (fun _ => false) = true
  · right
    have huniv : (Finset.univ.filter (fun x : Fin n → Bool => f x = true)) = Finset.univ := by
      apply Finset.filter_true_of_mem
      intro x _
      rw [hf x (fun _ => false)]
      exact h
    rw [huniv]
    simp
  · left
    rw [Finset.card_eq_zero]
    apply Finset.filter_false_of_mem
    intro x _
    rw [hf x (fun _ => false)]
    exact h

/-- A constant function and a balanced function are never the same function. -/
