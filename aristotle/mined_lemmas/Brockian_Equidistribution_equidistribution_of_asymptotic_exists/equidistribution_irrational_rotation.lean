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
# Equidistribution Of Asymptotic Exists
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: this Lean toolchain requires `import` to be the very first command in a file, so the
required header comment appears immediately after the import.)
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal Real BigOperators

namespace Brockian.Equidistribution

/-- The circle `ℝ / ℤ`, on which we study equidistribution. -/
abbrev Circ : Type := AddCircle (1 : ℝ)

noncomputable instance : IsProbabilityMeasure (volume : Measure Circ) := ⟨by simp⟩

/-- Continuous functions on the (compact) circle are integrable for any finite measure. -/

theorem equidistribution_irrational_rotation (al : ℝ) (hal : Irrational al)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    Tendsto (fun N : ℕ =>
        (((Finset.range N).filter
          (fun n : ℕ => a ≤ Int.fract ((n : ℝ) * al) ∧ Int.fract ((n : ℝ) * al) < b)).card : ℝ)
          / (N : ℝ))
      atTop (𝓝 (b - a)) := by
  refine equidistribution_of_asymptotic_exists (fun n : ℕ => (n : ℝ) * al)
    (fun h hh => ?_) a b ha hab hb
  simpa using tendsto_exp_average_irrational al hal h hh

end Brockian.Equidistribution

