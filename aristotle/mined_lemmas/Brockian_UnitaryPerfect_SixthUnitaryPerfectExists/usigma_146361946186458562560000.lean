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

theorem usigma_146361946186458562560000 : usigma 146361946186458562560000 = 292723892372917125120000 := by
  have h0 : usigma 1 = 1 := usigma_one
  have h1 : usigma 313 = 314 :=
    usigma_step (p := 313) (k := 1) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) h0 (by norm_num)
  have h2 : usigma 49141 = 49612 :=
    usigma_step (p := 157) (k := 1) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) h1 (by norm_num)
  have h3 : usigma 5356369 = 5457320 :=
    usigma_step (p := 109) (k := 1) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) h2 (by norm_num)
  have h4 : usigma 423153151 = 436585600 :=
    usigma_step (p := 79) (k := 1) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) h3 (by norm_num)
  have h5 : usigma 15656666587 = 16590252800 :=
    usigma_step (p := 37) (k := 1) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) h4 (by norm_num)
  have h6 : usigma 297476665153 = 331805056000 :=
    usigma_step (p := 19) (k := 1) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) h5 (by norm_num)
  have h7 : usigma 3867196646989 = 4645270784000 :=
    usigma_step (p := 13) (k := 1) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) h6 (by norm_num)
  have h8 : usigma 42539163116879 = 55743249408000 :=
    usigma_step (p := 11) (k := 1) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) h7 (by norm_num)
  have h9 : usigma 297774141818153 = 445945995264000 :=
    usigma_step (p := 7) (k := 1) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) h8 (by norm_num)
  have h10 : usigma 186108838636345625 = 279162193035264000 :=
    usigma_step (p := 5) (k := 4) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) h9 (by norm_num)
  have h11 : usigma 558326515909036875 = 1116648772141056000 :=
    usigma_step (p := 3) (k := 1) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) h10 (by norm_num)
  have h12 : usigma 146361946186458562560000 = 292723892372917125120000 :=
    usigma_step (p := 2) (k := 18) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) h11 (by norm_num)
  exact h12

/-- The five known unitary perfect numbers really are unitary perfect. -/
