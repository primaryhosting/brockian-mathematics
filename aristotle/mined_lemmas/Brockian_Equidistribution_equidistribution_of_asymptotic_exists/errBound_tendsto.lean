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

This file constructs an explicit sequence in `[0, 1)` whose empirical distribution is
asymptotically the uniform one: for every subinterval `[a, b) ⊆ [0, 1)` the proportion of
the first `N` terms lying in `[a, b)` converges to `b - a`.

The construction is the "triangular block" sequence
`0/1 ; 0/2, 1/2 ; 0/3, 1/3, 2/3 ; 0/4, …` .
-/

open Filter Topology

namespace Brockian.Equidistribution

/-- Triangular numbers: `tri k = 0 + 1 + ⋯ + k`. -/

lemma errBound_tendsto : Tendsto errBound atTop (𝓝 0) := by
  have h1 : Tendsto (fun N : ℕ => (3 * Real.sqrt 2 + 3) / Real.sqrt (N : ℝ)) atTop (𝓝 0) := by
    have hs : Tendsto (fun N : ℕ => Real.sqrt (N : ℝ)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    simpa [div_eq_mul_inv, mul_comm] using hs.inv_tendsto_atTop.const_mul (3 * Real.sqrt 2 + 3)
  refine squeeze_zero' (Eventually.of_forall ?_) ?_ h1
  · intro N
    unfold errBound
    positivity
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
    have hsq : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hNpos
    have hsqle : Real.sqrt (N : ℝ) ≤ (N : ℝ) := by
      nlinarith [Real.sq_sqrt (le_of_lt hNpos), Real.sqrt_nonneg (N : ℝ),
        Real.one_le_sqrt.2 hN1]
    have hmul : Real.sqrt (2 * N) = Real.sqrt 2 * Real.sqrt (N : ℝ) := by
      rw [← Real.sqrt_mul (by norm_num)]
    unfold errBound
    rw [hmul, div_le_div_iff₀ hNpos hsq]
    have hs2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    nlinarith [Real.sq_sqrt (le_of_lt hNpos), Real.sqrt_nonneg (N : ℝ)]

