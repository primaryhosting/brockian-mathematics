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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

import Mathlib

/-!
# Hyperperfect All K
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectAllK
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace Brockian.HyperperfectNumbers

/-! ## The notion of a `k`-hyperperfect number -/

/-- `IsHyperperfect k n` says that `n` is a `k`-hyperperfect number, i.e. `n > 1` and
`n = 1 + k * (σ n - n - 1)`, where `σ n` is the sum of the divisors of `n`.

The equation is written in the subtraction-free form `n + k * (n + 1) = k * σ n + 1`,
which is equivalent over `ℤ` to `n = 1 + k * (σ n - n - 1)`; this avoids the pitfalls of
truncated natural subtraction (which would make `n = 1` a spurious solution). -/

theorem isHyperperfect_iff_int (k n : ℕ) :
    IsHyperperfect k n ↔ 1 < n ∧ (n : ℤ) = 1 + k * ((σ 1 n : ℤ) - n - 1) := by
  rw [IsHyperperfect]
  constructor
  · rintro ⟨hn, h⟩
    refine ⟨hn, ?_⟩
    have := congrArg (fun t : ℕ => (t : ℤ)) h
    push_cast at this
    linarith
  · rintro ⟨hn, h⟩
    refine ⟨hn, ?_⟩
    have : ((n + k * (n + 1) : ℕ) : ℤ) = ((k * (σ 1 n) + 1 : ℕ) : ℤ) := by push_cast; linarith
    exact_mod_cast this

/-! ## A divisor-sum-free reformulation

The Brockian hyperperfect conjecture asserts that a `k`-hyperperfect number exists for
every `k ≥ 1`.  We reformulate it as an equivalent statement in which the divisor-sum
function `σ` has been eliminated: instead of a number `n`, one asks for a finite set of
primes together with exponents, and the hyperperfection equation becomes an explicit
polynomial equation in the primes and their geometric sums. -/

/-- `PrimeExpo S e` says that `S` is a finite set of primes and `e` is positive on `S`. -/
