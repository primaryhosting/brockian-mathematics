/-
# Psi Two Le
Category: Frontier Wave 2 (deeper machinery)
Target: Chebyshev.psi_two_le
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Psi Two Le
Category: Frontier Wave 2 (deeper machinery)
Target: Chebyshev.psi_two_le
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

namespace Chebyshev

open ArithmeticFunction

/-- `Λ 4 = log 2`, since `4 = 2 ^ 2` is a prime power with smallest prime factor `2`. -/

lemma vonMangoldt_four : Λ 4 = Real.log 2 := by
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num, vonMangoldt_apply_pow two_ne_zero,
    vonMangoldt_apply_prime Nat.prime_two]
  norm_num

/-- The second Chebyshev function at `4`:
`ψ(4) = Λ 1 + Λ 2 + Λ 3 + Λ 4 = 0 + log 2 + log 3 + log 2 = log 12`. -/
