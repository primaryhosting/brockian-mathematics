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

theorem usigma_60 : usigma 60 = 120 := by
  have h0 : usigma 1 = 1 := usigma_one
  have h1 : usigma 5 = 6 :=
    usigma_step (p := 5) (k := 1) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) h0 (by norm_num)
  have h2 : usigma 15 = 24 :=
    usigma_step (p := 3) (k := 1) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) h1 (by norm_num)
  have h3 : usigma 60 = 120 :=
    usigma_step (p := 2) (k := 2) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) h2 (by norm_num)
  exact h3

