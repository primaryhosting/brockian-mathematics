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

theorem not_isOreHarmonic_primePow (hp : p.Prime) (hk : 0 < k) :
    ¬ IsOreHarmonic (p ^ k) := by
  rintro ⟨-, hdvd⟩
  rw [numDivisors_primePow hp] at hdvd
  have hcop : Nat.Coprime (divisorSum (p ^ k)) (p ^ k) :=
    (coprime_divisorSum_primePow hp k).pow_right k
  have hdvd' : divisorSum (p ^ k) ∣ (k + 1) := hcop.dvd_of_dvd_mul_left hdvd
  have hle : divisorSum (p ^ k) ≤ k + 1 := Nat.le_of_dvd (Nat.succ_pos k) hdvd'
  have hge : 1 + p ^ k ≤ divisorSum (p ^ k) := le_divisorSum_primePow hp hk
  have hlt : k < p ^ k := Nat.lt_pow_self hp.one_lt
  omega

/-- An odd Ore harmonic number greater than `1` is not a prime power. -/
