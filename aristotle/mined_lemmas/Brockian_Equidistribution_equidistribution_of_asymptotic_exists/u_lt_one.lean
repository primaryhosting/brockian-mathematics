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
# Equidistribution Of Asymptotic Exists
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Equidistribution Of Asymptotic Exists
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Finset

namespace Brockian.Equidistribution

/-- Triangular numbers: `T m = 1 + 2 + ⋯ + m = m (m+1) / 2`. -/

lemma u_lt_one (n : ℕ) : u n < 1 := by
  have h1 : (n - T (blk n) : ℕ) < blk n + 1 := by
    have h2 := lt_T_blk_succ n
    have h3 := T_blk_le n
    have h4 := T_succ (blk n)
    omega
  have hpos : (0:ℝ) < (blk n : ℝ) + 1 := by positivity
  rw [u, div_lt_one hpos]
  exact_mod_cast h1

/-- The counting function: how many of `u 0, …, u (N-1)` lie in `[a, b)`. -/
