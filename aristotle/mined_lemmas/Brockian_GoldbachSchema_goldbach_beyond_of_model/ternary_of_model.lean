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

set_option maxHeartbeats 4000000
set_option maxRecDepth 20000000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian.GoldbachSchema

/-! ## The statements -/

/-- `GoldbachPair n` : `n` is a sum of two primes. -/

theorem ternary_of_model {N : ℕ} (model : GoldbachModel N) :
    ∀ n : ℕ, Odd n → 9 ≤ n → n ≤ N + 3 → TernaryRep n := by
  intro n hodd h9 hle
  obtain ⟨k, hk⟩ := hodd
  have heven : Even (n - 3) := ⟨k - 1, by omega⟩
  obtain ⟨p, q, hp, hq, hpq⟩ := model (n - 3) (by omega) (by omega) heven
  exact ⟨p, q, 3, hp, hq, Nat.prime_three, by omega⟩

/-! ## A kernel-checkable primality certificate -/

/-- `noDiv n k = true` iff no `m` with `2 ≤ m ≤ k` divides `n`. -/
