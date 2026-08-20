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
# Triangular Mod 5 Mem
Category: Cone Line
Target: Brockian.ConeLine.triangular_mod5_mem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.ConeLine

/-- The `n`-th triangular number, `T n = n(n+1)/2` (natural-number division). -/

lemma T_ten_mul_add (q r : ℕ) : T (10 * q + r) = 50 * q * q + 5 * q * (2 * r + 1) + T r := by
  have h1 : 2 * T (10 * q + r) = (10 * q + r) * (10 * q + r + 1) := two_mul_T _
  have h2 : 2 * T r = r * (r + 1) := two_mul_T r
  have h3 : (10 * q + r) * (10 * q + r + 1)
      = 2 * (50 * q * q + 5 * q * (2 * r + 1)) + r * (r + 1) := by ring
  omega

/-- On the first period, the triangular residues are `0`, `1`, `3`. -/
