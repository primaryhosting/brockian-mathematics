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

theorem not_constant_and_balanced (f : (Fin n → Bool) → Bool) :
    ¬ (IsConstant f ∧ IsBalanced f) := by
  rintro ⟨hc, hb⟩
  have hp : 0 < 2 ^ n := Nat.two_pow_pos n
  rw [IsBalanced] at hb
  rcases card_true_of_constant f hc with h | h <;> rw [h] at hb <;> omega

/-- For a constant `f`, the all-zero outcome has amplitude of modulus one. -/
