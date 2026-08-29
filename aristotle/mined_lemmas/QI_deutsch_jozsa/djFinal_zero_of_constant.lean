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

theorem djFinal_zero_of_constant (f : (Fin n → Bool) → Bool) (hf : IsConstant f) :
    ‖djFinal f (zeroState n)‖ = 1 := by
  have hne : ((2 : ℂ) ^ n) ≠ 0 := pow_ne_zero n two_ne_zero
  rw [djFinal_zero, sum_sgn]
  rcases card_true_of_constant f hf with h | h <;> rw [h]
  · rw [Nat.cast_zero, mul_zero, sub_zero, one_div, inv_mul_cancel₀ hne, norm_one]
  · push_cast
    rw [show (1 / (2 : ℂ) ^ n) * ((2 : ℂ) ^ n - 2 * (2 : ℂ) ^ n) = -1 by field_simp; norm_num]
    norm_num

/-- For a balanced `f`, the all-zero outcome has amplitude zero. -/
