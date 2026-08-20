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

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

namespace Brockian.OreHarmonicNumbers

open ArithmeticFunction

/-- `n` is an *Ore harmonic number* (harmonic divisor number) if it is positive and the
harmonic mean of its divisors, namely `n * τ n / σ n`, is an integer.  Equivalently,
`σ 1 n ∣ n * σ 0 n`. -/

theorem odd_isOreHarmonic_lt_300 :
    ∀ n ∈ Finset.range 300, IsOreHarmonic n → Odd n → n = 1 := by
  simp only [IsOreHarmonic, ArithmeticFunction.sigma_one_apply,
    ArithmeticFunction.sigma_zero_apply, Nat.odd_iff]
  decide

end Brockian.OreHarmonicNumbers

