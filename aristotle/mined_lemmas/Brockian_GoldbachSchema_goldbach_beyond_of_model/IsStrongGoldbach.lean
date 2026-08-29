import Brockian.GoldbachSchema

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
# Goldbach Beyond Of Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_beyond_of_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxRecDepth 100000

namespace Brockian
namespace GoldbachSchema

/-- The Goldbach property: `n` is a sum of two primes. -/

theorem IsStrongGoldbach.isGoldbach {n : ℕ} (h : IsStrongGoldbach n) : IsGoldbach n := by
  obtain ⟨p, q, hp, hq, _, _, _, hsum⟩ := h
  exact ⟨p, q, hp, hq, hsum⟩

/-- A *model of the Goldbach schema beyond `N`*: a concrete even number `n > N`
together with a certified representation of `n` as a sum of two distinct odd primes. -/
structure Model (N : ℕ) where
  /-- The even number witnessing the schema. -/
  n : ℕ
  /-- The first prime summand. -/
  p : ℕ
  /-- The second prime summand. -/
  q : ℕ
  /-- The witness lies beyond the scale `N`. -/
  lt : N < n
  /-- The witness is even. -/
  even : Even n
  /-- `p` is prime. -/
  hp : Nat.Prime p
  /-- `q` is prime. -/
  hq : Nat.Prime q
  /-- `p` is odd. -/
  hp_odd : Odd p
  /-- `q` is odd. -/
  hq_odd : Odd q
  /-- The two prime summands are distinct. -/
  hne : p ≠ q
  /-- `n` is the sum of the two primes. -/
  hsum : n = p + q

/-- **Discharge of the named hypothesis.**  The Goldbach schema admits a model beyond
every scale `N`: given `N`, pick a prime `p ≥ max (N + 1) 5` and take `n = p + 3`. -/
