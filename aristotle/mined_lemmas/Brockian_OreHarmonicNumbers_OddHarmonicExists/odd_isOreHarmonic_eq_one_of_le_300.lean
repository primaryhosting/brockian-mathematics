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

namespace Brockian.OreHarmonicNumbers

/-- `IsOreHarmonic n` says that `n` is an *Ore harmonic number* (harmonic divisor number):
`n` is positive and the harmonic mean of its divisors, `n * τ(n) / σ(n)`, is an integer.
Here `τ n = n.divisors.card` is the number of divisors and `σ n = ∑ d ∈ n.divisors, d`
is their sum. -/

theorem odd_isOreHarmonic_eq_one_of_le_300 (n : ℕ) (hn : n ≤ 300) (hodd : Odd n)
    (h : IsOreHarmonic n) : n = 1 := by
  have key : ∀ m ∈ Finset.Icc 1 300, Odd m →
      (∑ d ∈ m.divisors, d) ∣ m * m.divisors.card → m = 1 := by decide
  exact key n (Finset.mem_Icc.mpr ⟨h.1, hn⟩) hodd h.2

end Brockian.OreHarmonicNumbers

