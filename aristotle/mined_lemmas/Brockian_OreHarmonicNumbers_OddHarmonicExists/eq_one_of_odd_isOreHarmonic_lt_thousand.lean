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

theorem eq_one_of_odd_isOreHarmonic_lt_thousand (n : ℕ) (hn : n < 1000) (hodd : Odd n)
    (h : IsOreHarmonic n) : n = 1 := by
  have key : ∀ m < 1000, m % 2 = 1 →
      ((∑ d ∈ m.divisors, d) ∣ m * m.divisors.card) → m = 1 := by decide
  exact key n hn (Nat.odd_iff.mp hodd) ((isOreHarmonic_iff n h.1).mp h)

end FiniteCheck

end Brockian.OreHarmonicNumbers

