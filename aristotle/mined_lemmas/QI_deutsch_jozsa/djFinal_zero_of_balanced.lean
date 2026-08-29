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

theorem djFinal_zero_of_balanced (f : (Fin n → Bool) → Bool) (hf : IsBalanced f) :
    djFinal f (zeroState n) = 0 := by
  rw [djFinal_zero, sum_sgn]
  have : ((2 * (Finset.univ.filter (fun x : Fin n → Bool => f x = true)).card : ℕ) : ℂ)
      = ((2 ^ n : ℕ) : ℂ) := by
    rw [hf]
  push_cast at this
  rw [← this]
  ring

/-! ## Main theorem -/

/-- **Deutsch–Jozsa.**  Given the promise that `f : (Fin n → Bool) → Bool` is
either constant or balanced, a single query to the oracle suffices to decide
which: after one query and a Hadamard transform, the all-zero measurement
outcome occurs with probability `1` exactly when `f` is constant, and with
probability `0` exactly when `f` is balanced. -/
