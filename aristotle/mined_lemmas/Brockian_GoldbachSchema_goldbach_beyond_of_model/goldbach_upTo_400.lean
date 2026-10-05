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

/-
# Goldbach Beyond Of Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_beyond_of_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Goldbach Beyond Of Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_beyond_of_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Scope of what is proved here

* `goldbach_beyond_of_model` is proved unconditionally (no hypothesis beyond the model datum):
  given a *model* certifying Goldbach's conjecture on a finite initial range `[4, N]`, the full
  conjecture is equivalent to its "beyond `N`" form.
* A model for `N = 400` (`model400`) is constructed and proved by kernel computation, so
  `goldbach_iff_beyond_400` is likewise unconditional.
* Goldbach's conjecture itself (`Goldbach`) is *not* proved here; it is an open problem, and
  nothing in this file asserts it.  Everything stated is either unconditional or explicitly
  conditional on `Goldbach` (see `ternary_of_goldbach`).
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Brockian.GoldbachSchema

/-- `IsGoldbach n` : the natural number `n` is a sum of two primes. -/

theorem goldbach_upTo_400 :
    ∀ n : ℕ, 4 ≤ n → n ≤ 400 → Even n → IsGoldbach n := by
  have key : ∀ n ∈ Finset.range 401, 4 ≤ n → n % 2 = 0 →
      ∃ p ∈ Finset.range (n + 1), Nat.Prime p ∧ Nat.Prime (n - p) := by decide
  intro n hn hle hev
  have hn2 : n % 2 = 0 := Nat.even_iff.mp hev
  obtain ⟨p, hp, hpp, hqp⟩ := key n (Finset.mem_range.mpr (by omega)) hn hn2
  have hple : p ≤ n := by
    have := Finset.mem_range.mp hp
    omega
  exact ⟨p, n - p, hpp, hqp, by omega⟩

/-- An explicit Goldbach model up to `400`. -/
