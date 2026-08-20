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

theorem isOreHarmonic_six : IsOreHarmonic 6 :=
  ⟨by norm_num, 2, by decide⟩

/-- There exists an odd Ore harmonic number, namely `n = 1`.

(Ore's conjecture asserts that `1` is the *only* odd harmonic divisor number; the existence
statement proved here is witnessed by `1` itself.) -/
