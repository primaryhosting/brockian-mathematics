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

namespace Brockian.HyperperfectNumbers

open Finset

/-- `Hyperperfect k n` says that `n` is a *`k`-hyperperfect number*, i.e. `n > 1` and
`n = 1 + k * (σ(n) - n - 1)`, where `σ(n) = ∑ d ∣ n, d`.

The defining equation is written in the subtraction-free form
`(k + 1) * n + k = k * σ(n) + 1`, which over the integers is equivalent to
`n = 1 + k * (σ n - n - 1)`. -/

theorem hyperperfect_iff_int (k n : ℕ) :
    Hyperperfect k n ↔
      1 < n ∧ (n : ℤ) = 1 + k * ((∑ d ∈ n.divisors, (d : ℤ)) - n - 1) := by
  constructor
  · rintro ⟨hn, h⟩
    refine ⟨hn, ?_⟩
    have h' : (((k + 1) * n + k : ℕ) : ℤ)
        = ((k * (∑ d ∈ n.divisors, d) + 1 : ℕ) : ℤ) := by
      exact_mod_cast congrArg (fun m : ℕ => (m : ℤ)) h
    push_cast at h'
    linarith
  · rintro ⟨hn, h⟩
    refine ⟨hn, ?_⟩
    have : (((k + 1) * n + k : ℕ) : ℤ) = ((k * (∑ d ∈ n.divisors, d) + 1 : ℕ) : ℤ) := by
      push_cast
      linarith
    exact_mod_cast this

/-- The sum of divisors of a product of two distinct primes. -/
