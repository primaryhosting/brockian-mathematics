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
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

variable {n : ℕ}

/-- The sign `(-1)^b` attached to a Boolean value. -/

lemma sum_sign_of_constant {f : (Fin n → Bool) → Bool} (hf : IsConstant f) :
    ∑ x : Fin n → Bool, sign (f x) = (2 ^ n : ℂ) * sign (f (zeroStr n)) := by
  have : ∀ x ∈ (Finset.univ : Finset (Fin n → Bool)), sign (f x) = sign (f (zeroStr n)) := by
    intro x _; rw [hf x (zeroStr n)]
  rw [Finset.sum_congr rfl this, Finset.sum_const, card_bitstrings, nsmul_eq_mul]
  push_cast
  ring

