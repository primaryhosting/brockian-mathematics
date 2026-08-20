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
# Sixth Unitary Perfect Exists
Category: Brockian Conjecture
Target: Brockian.UnitaryPerfect.SixthUnitaryPerfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.UnitaryPerfect

open Finset

/-- The unitary divisors of `n`: the divisors `d` of `n` with `gcd d (n / d) = 1`. -/

lemma even_usigma_of_odd {n : ℕ} (hodd : Odd n) (hn : 1 < n) : Even (usigma n) := by
  obtain ⟨q, m, hq1, hqm, -, hus⟩ := usigma_split hn
  have hqodd : Odd q := odd_of_dvd_odd ⟨m, hqm.symm⟩ hodd
  rw [hus]
  exact (hqodd.add_one).mul_right _

/-- **Key lemma**: there is no odd unitary perfect number. -/
