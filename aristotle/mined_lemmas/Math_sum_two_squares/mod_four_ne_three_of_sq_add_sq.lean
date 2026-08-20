import Mathlib

/-!
# Sum Two Squares
Category: Pure Mathematics
Target: Math.sum_two_squares
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

namespace Math

/-- A perfect square is congruent to `0` or `1` modulo `4`. -/

theorem mod_four_ne_three_of_sq_add_sq {n a b : ℕ} (h : n = a ^ 2 + b ^ 2) : n % 4 ≠ 3 := by
  have ha := sq_mod_four_eq_zero_or_one a
  have hb := sq_mod_four_eq_zero_or_one b
  have hmod := Nat.add_mod (a ^ 2) (b ^ 2) 4
  omega

/-- **Fermat's two-square theorem**: a prime `p` is a sum of two squares if and only if
`p = 2` or `p ≡ 1 [MOD 4]`.  (The hard direction uses `Nat.Prime.sq_add_sq` from Mathlib.) -/
