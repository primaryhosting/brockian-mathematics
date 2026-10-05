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
# Goldbach Beyond Of Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_beyond_of_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Goldbach Beyond Of Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_beyond_of_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000

namespace Brockian
namespace GoldbachSchema

/-- The finite set of *Goldbach representations* of `n`: those `p ≤ n` such that both `p`
and `n - p` are prime. -/

theorem lower_bound_pos {c : ℝ} (hc : 0 < c) {n : ℕ} (hn : 4 ≤ n) :
    0 < c * (n : ℝ) / (Real.log n) ^ 2 := by
  have hn1 : (1 : ℝ) < (n : ℝ) := by
    have : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hlog : 0 < Real.log n := Real.log_pos hn1
  have hsq : 0 < (Real.log n) ^ 2 := by positivity
  have hnum : 0 < c * (n : ℝ) := by nlinarith
  exact div_pos hnum hsq

/-- **Goldbach beyond a threshold, from a counting model.**

If a Hardy–Littlewood style lower-bound model `M` for the number of Goldbach
representations is available, then every even `n ≥ M.bound` really is a sum of two primes.

The statement is unconditional: it carries no ambient hypothesis besides the model data
itself, and its proof uses no additional assumptions. -/
