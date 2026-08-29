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
# Equidistribution Of BV Uniform
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.equidistribution_of_BV_uniform
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Filter Finset MeasureTheory
open scoped Topology

namespace Brockian
namespace EquidistributionBVReduction

/-- A sequence `x : ℕ → ℝ` with values in `[0, 1)` is *uniformly distributed* if for every
`c ∈ [0, 1]` the proportion of the first `N` terms lying in `[0, c)` tends to `c`. -/

lemma le_integral_of_monotone {g : ℝ → ℝ} (hg : Monotone g) {a b : ℝ} (hab : a ≤ b) :
    (b - a) * g a ≤ ∫ t in a..b, g t := by
  have hi : IntervalIntegrable g MeasureTheory.volume a b := hg.intervalIntegrable
  have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
    (f := fun _ => g a) (g := g) hab intervalIntegrable_const hi (fun t ht => hg ht.1)
  simpa [mul_comm] using h

section Monotone

variable {x : ℕ → ℝ} {g : ℝ → ℝ}

/-- Approximation at scale `k`: the Birkhoff averages of a monotone function along a uniformly
distributed sequence are eventually within `(g 1 - g 0) / k + ε` of the integral. -/
