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

theorem hyperperfect_of_factorization {k d e : ℕ} (hk : 1 ≤ k) (hde : d * e = k ^ 2 + 1)
    (hp : (k + d).Prime) (hq : (k + e).Prime) : Hyperperfect k ((k + d) * (k + e)) := by
  have hne : d ≠ e := by
    rintro rfl
    rcases Nat.lt_or_ge d (k + 1) with h | h
    · nlinarith
    · nlinarith
  rw [hyperperfect_mul_primes_iff hp hq (by omega)]
  nlinarith [hde]

/-- **Sharpness of the construction.** For `k ≥ 1`, a `k`-hyperperfect number that is a product
of two distinct primes exists *exactly* when `k ^ 2 + 1` factors as `d * e` with `k + d` and
`k + e` both prime. -/
