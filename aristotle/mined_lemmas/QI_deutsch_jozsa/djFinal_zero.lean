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

theorem djFinal_zero (f : (Fin n → Bool) → Bool) :
    djFinal f (zeroState n) = (1 / (2 : ℂ) ^ n) * ∑ x : Fin n → Bool, sgn (f x) := by
  have h2 : (1 / ((Real.sqrt (2 ^ n) : ℝ) : ℂ)) * (1 / ((Real.sqrt (2 ^ n) : ℝ) : ℂ))
      = 1 / (2 : ℂ) ^ n := by
    rw [div_mul_div_comm, sqrt_two_pow_sq]
    norm_num
  simp only [djFinal, hadamard, phaseOracleState, uniform, zeroState, Bool.and_false, sgn,
    Bool.false_eq_true, if_false, Finset.prod_const_one, one_mul, ← Finset.sum_mul]
  linear_combination (∑ x : Fin n → Bool, (if f x = true then (-1 : ℂ) else 1)) * h2

