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

import Mathlib

/-!
# Counting Diverges Of Discrete And Weyl Law Match
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_discrete_and_WeylLawMatch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Topology Set

namespace Brockian.Weyl.WeylLawTarget

/-- The spectral counting function of a set `S ⊆ ℝ` (thought of as the spectrum of an
operator, listed without multiplicity): `spectralCounting S t` is the number of spectral
points that are `≤ t`. -/

theorem counting_tendsto_atTop_of_WeylLawMatch {S : Set ℝ} {C d : ℝ} (hC : 0 < C) (hd : 0 < d)
    (hweyl : WeylLawMatch S C d) :
    Tendsto (fun t : ℝ => (spectralCounting S t : ℝ)) atTop atTop := by
  have hpow : Tendsto (fun t : ℝ => t ^ (d / 2)) atTop atTop :=
    tendsto_rpow_atTop (by linarith)
  have hX : Tendsto (fun t : ℝ => C * t ^ (d / 2)) atTop atTop := hpow.const_mul_atTop hC
  have key :
      Tendsto (fun t : ℝ =>
        ((spectralCounting S t : ℝ) / (C * t ^ (d / 2))) * (C * t ^ (d / 2))) atTop atTop :=
    hweyl.pos_mul_atTop one_pos hX
  refine key.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have hne : C * t ^ (d / 2) ≠ 0 := by positivity
  field_simp

/-- If the counting function of `S` diverges, then `S` is infinite. -/
