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

theorem sum_sgn (f : (Fin n → Bool) → Bool) :
    (∑ x : Fin n → Bool, sgn (f x))
      = (2 : ℂ) ^ n - 2 * ((Finset.univ.filter (fun x : Fin n → Bool => f x = true)).card : ℂ) := by
  have h : ∀ x : Fin n → Bool, sgn (f x) = 1 - 2 * (if f x = true then (1 : ℂ) else 0) := by
    intro x
    simp only [sgn]
    split <;> norm_num
  simp only [h, Finset.sum_sub_distrib, Finset.sum_const, ← Finset.mul_sum, Finset.sum_boole]
  simp [Finset.card_univ]

/-- The amplitude of the all-zero outcome after one query. -/
