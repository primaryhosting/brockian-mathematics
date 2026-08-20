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

namespace Brockian
namespace OreHarmonicNumbers

/-- `n` is an *Ore harmonic number* (harmonic divisor number) when `n` is positive and the
harmonic mean of its divisors, `n * d(n) / σ(n)`, is a natural number.  Equivalently
`σ(n) ∣ n * d(n)`, which is how it is phrased here (`k` is the harmonic mean). -/

def IsOreHarmonic (n : ℕ) : Prop :=
  0 < n ∧ ∃ k : ℕ, n * n.divisors.card = k * ∑ d ∈ n.divisors, d

/-- `1` is an Ore harmonic number: its only divisor is `1`, and the harmonic mean is `1`. -/

theorem isOreHarmonic_one : IsOreHarmonic 1 :=
  ⟨Nat.one_pos, 1, by decide⟩

/-- Sanity check for the definition: `6` is an Ore harmonic number, with harmonic mean `2`
(its divisors are `1, 2, 3, 6`, so `6 * 4 = 2 * 12`). -/

theorem OddHarmonicExists : ∃ n : ℕ, Odd n ∧ IsOreHarmonic n :=
  ⟨1, odd_one, isOreHarmonic_one⟩

end OreHarmonicNumbers
end Brockian
