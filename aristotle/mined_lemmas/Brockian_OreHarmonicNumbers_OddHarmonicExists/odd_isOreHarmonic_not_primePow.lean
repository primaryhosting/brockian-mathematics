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
# Odd Harmonic Exists
Category: Brockian Conjecture
Target: Brockian.OreHarmonicNumbers.OddHarmonicExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Odd Harmonic Exists
Category: Brockian Conjecture
Target: Brockian.OreHarmonicNumbers.OddHarmonicExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Brockian.OreHarmonicNumbers

/-- The sum of the divisors of `n`, usually written `σ n`. -/

theorem odd_isOreHarmonic_not_primePow {n : ℕ} (hharm : IsOreHarmonic n) :
    ¬ ∃ p k : ℕ, p.Prime ∧ 0 < k ∧ n = p ^ k := by
  rintro ⟨p, k, hp, hk, rfl⟩
  exact not_isOreHarmonic_primePow hp hk hharm

end PrimePow

set_option maxRecDepth 40000 in
set_option maxHeartbeats 1000000 in
/-- Verified partial case of Ore's conjecture: there is no odd Ore harmonic number `n`
with `2 ≤ n ≤ 1000`. -/
