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

namespace Brockian.OreHarmonicNumbers

/-- The harmonic mean of the (positive) divisors of `n`:
`τ(n) / ∑_{d ∣ n} 1/d`. -/

theorem divisorHarmonicMean_eq (n : ℕ) (hn : 0 < n) :
    divisorHarmonicMean n = (n : ℚ) * n.divisors.card / (∑ d ∈ n.divisors, (d : ℚ)) := by
  have hn0 : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [divisorHarmonicMean, sum_inv_divisors, div_div_eq_mul_div]
  ring_nf

/-- Divisibility characterisation of Ore harmonic numbers: `n` is harmonic iff
`σ(n) ∣ n · τ(n)`. -/
