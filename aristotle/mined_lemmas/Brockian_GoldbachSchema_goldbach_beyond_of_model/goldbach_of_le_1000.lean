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

open scoped BigOperators
open scoped Nat

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian
namespace GoldbachSchema

/-- Goldbach's property at `n`: `n` is a sum of two primes. -/

theorem goldbach_of_le_1000 (n : ℕ) (h4 : 4 ≤ n) (hn : n ≤ 1000) (he : Even n) : Goldbach n := by
  obtain ⟨m, hm⟩ := he
  have hk : (n - 4) / 2 < 499 := by omega
  obtain ⟨p, hp, hple, hq⟩ := smallPrimes_split ((n - 4) / 2) hk
  have hn' : 2 * ((n - 4) / 2) + 4 = n := by omega
  rw [hn'] at hple hq
  exact ⟨p, n - p, smallPrimes_prime p hp, smallPrimes_prime _ hq, by omega⟩

/-- **Main target.**  If the (open) model hypothesis holds beyond some threshold `B ≤ 1000`,
then Goldbach's conjecture holds for *every* even `n ≥ 4`.

The finite hypothesis of the original schema — that Goldbach's conjecture has been checked on
the range `4 ≤ n ≤ 1000` — is discharged here (see `goldbach_of_le_1000`), so no verification
assumption remains; the only remaining hypothesis is the genuinely open statement
`GoldbachModel B` about the numbers beyond the checked range. -/
