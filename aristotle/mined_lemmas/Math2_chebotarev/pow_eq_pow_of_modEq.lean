/-
# Chebotarev
Category: Frontier Math
Target: Math2.chebotarev
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Chebotarev
Category: Frontier Math
Target: Math2.chebotarev
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

namespace Math2

/-- `IsFrobeniusAt R σ p` says that the ring automorphism `σ` of `R` is a Frobenius
automorphism at the rational prime `p`: there is a maximal ideal `P` of `R` lying above `p`
such that `σ x ≡ x ^ p (mod P)` for all `x : R`.

For `R` the ring of integers of a Galois number field this is the usual notion of (an element
of) the Frobenius conjugacy class at `p`. -/

theorem pow_eq_pow_of_modEq (hζ : IsPrimitiveRoot ζ n) {i j : ℕ} (h : i ≡ j [MOD n]) :
    ζ ^ i = ζ ^ j := by
  have key : ∀ k : ℕ, ζ ^ k = ζ ^ (k % n) := by
    intro k
    conv_lhs => rw [← Nat.div_add_mod k n]
    rw [pow_add, pow_mul, hζ.pow_eq_one, one_pow, one_mul]
  rw [key i, key j, h]

omit [CharZero R] in
/-- In `ℤ[ζ]` with `ζ` a primitive `n`-th root of unity, every ring automorphism sends `ζ`
to a power `ζ ^ a` with `a` coprime to `n`. -/
