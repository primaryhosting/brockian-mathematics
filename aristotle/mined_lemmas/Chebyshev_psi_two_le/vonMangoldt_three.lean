/-
# Psi Two Le
Category: Frontier Wave 2 (deeper machinery)
Target: Chebyshev.psi_two_le
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

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

/-- Λ(1) = 0. -/

theorem vonMangoldt_three : Λ 3 = Real.log 3 := by
  rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three]
  norm_num

/-- Λ(4) = log 2, since 4 = 2². -/
