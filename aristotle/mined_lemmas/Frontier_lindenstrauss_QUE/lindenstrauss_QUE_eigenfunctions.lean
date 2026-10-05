import Mathlib

/-!
# Lindenstrauss QUE
Category: Frontier — Fields Medal Work
Target: Frontier.lindenstrauss_QUE
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

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- A *quantum limit* of a sequence of probability measures `mu` is a weak-* limit of some
subsequence of `mu`.  In the arithmetic setting, `mu n` is the microlocal lift of the `n`-th Hecke
eigenform and its quantum limits are the measures classified by Lindenstrauss's measure rigidity
theorem. -/

theorem lindenstrauss_QUE_eigenfunctions (vol : ProbabilityMeasure X)
    (psi : ℕ → X → ℂ) (hpsi : ∀ n, Measurable (psi n)) (mu : ℕ → ProbabilityMeasure X)
    (hmu : ∀ n, (mu n : Measure X)
      = (vol : Measure X).withDensity (fun x => ((‖psi n x‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞)))
    (hrigid : ∀ nu : ProbabilityMeasure X, IsQuantumLimit mu nu → nu = vol) (f : C(X, ℝ)) :
    Tendsto (fun n => ∫ x, ‖psi n x‖ ^ 2 * f x ∂(vol : Measure X)) atTop
      (𝓝 (∫ x, f x ∂(vol : Measure X))) := by
  have key := lindenstrauss_QUE_integral vol mu hrigid (BoundedContinuousFunction.mkOfCompact f)
  refine key.congr (fun n => ?_)
  have hmeas : Measurable (fun x => (‖psi n x‖₊ ^ 2 : ℝ≥0)) :=
    ((hpsi n).nnnorm).pow_const 2
  rw [hmu n, integral_withDensity_eq_integral_smul hmeas]
  simp [NNReal.smul_def]

end Frontier

