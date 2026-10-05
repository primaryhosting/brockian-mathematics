/-
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

/-- The radical of a natural number: the product of its distinct prime divisors. -/

lemma rad_le_of_lt (ε K r : ℝ) (hε : 0 < ε) (hr : 1 ≤ r)
    (h : r ^ (1 + ε) < K * r ^ (1 + ε / 2)) :
    r ≤ Real.exp (2 * Real.log K / ε) := by
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le zero_lt_one hr
  have hsplit : r ^ (1 + ε) = r ^ (1 + ε / 2) * r ^ (ε / 2) := by
    rw [← Real.rpow_add hr0]
    ring_nf
  have hpos : (0 : ℝ) < r ^ (1 + ε / 2) := Real.rpow_pos_of_pos hr0 _
  have hK : r ^ (ε / 2) < K := by
    have := hsplit ▸ h
    nlinarith [this]
  have hK0 : (0 : ℝ) < K := lt_of_lt_of_le (Real.rpow_pos_of_pos hr0 _) hK.le
  have hlog : (ε / 2) * Real.log r < Real.log K := by
    have h1 : Real.log (r ^ (ε / 2)) < Real.log K :=
      Real.log_lt_log (Real.rpow_pos_of_pos hr0 _) hK
    rwa [Real.log_rpow hr0] at h1
  have hlogr : Real.log r < 2 * Real.log K / ε := by
    rw [lt_div_iff₀ hε]
    nlinarith
  calc r = Real.exp (Real.log r) := (Real.exp_log hr0).symm
    _ ≤ Real.exp (2 * Real.log K / ε) := Real.exp_le_exp.2 hlogr.le

