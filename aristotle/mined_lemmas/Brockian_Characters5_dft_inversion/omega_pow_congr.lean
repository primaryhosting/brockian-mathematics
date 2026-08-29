import Mathlib

/-!
# Dft Inversion
Category: Characters
Target: Brockian.Characters5.dft_inversion
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

namespace Brockian
namespace Characters5

/-- A primitive fifth root of unity. -/

lemma omega_pow_congr {m n : ℕ} (h : m % 5 = n % 5) : omega ^ m = omega ^ n := by
  conv_lhs => rw [← Nat.div_add_mod m 5]
  conv_rhs => rw [← Nat.div_add_mod n 5]
  rw [pow_add, pow_add, pow_mul, pow_mul, omega_pow_five, one_pow, one_pow, h]

