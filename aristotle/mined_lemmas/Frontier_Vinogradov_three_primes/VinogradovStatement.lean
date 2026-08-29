import Mathlib

/-!
# Vinogradov Three Primes
Category: Frontier — Prime Numbers
Target: Frontier.Vinogradov_three_primes
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

/-- `IsSumOfThreePrimes n` means that `n` can be written as a sum of three
(not necessarily distinct) prime numbers. -/

def VinogradovStatement : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Odd n → IsSumOfThreePrimes n

/-- The binary Goldbach conjecture: every even number `≥ 4` is a sum of two primes. -/
