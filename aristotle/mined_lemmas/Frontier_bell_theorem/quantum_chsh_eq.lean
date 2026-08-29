import Mathlib

/-!
# Bell Theorem
Category: Frontier Physics
Target: Frontier.bell_theorem
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

open MeasureTheory

/-! ## Local hidden-variable models

A local hidden-variable (LHV) model for a bipartite experiment with two measurement
settings per side consists of:

* a probability space `(Λ, μ)` of hidden variables;
* for each of Alice's two settings `i : Bool`, a response function `A i : Λ → ℝ`
  taking values in `[-1, 1]`, depending only on Alice's setting and the hidden variable
  (this is the locality/no-signalling assumption: `A i λ` does not depend on Bob's
  setting `j`, and symmetrically for `B`);
* likewise for Bob, `B j : Λ → ℝ` with values in `[-1, 1]`.

The measured correlation for settings `(i, j)` is `∫ λ, A i λ * B j λ ∂μ`.
-/

/-- `IsLHV μ A B` says that `(μ, A, B)` is a local hidden-variable model:
`μ` is a probability measure on the hidden variables, the response functions are
measurable, and they take values in `[-1, 1]`. -/
structure IsLHV {Λ : Type*} [MeasurableSpace Λ] (μ : Measure Λ)
    (A B : Bool → Λ → ℝ) : Prop where
  isProbabilityMeasure : IsProbabilityMeasure μ
  measA : ∀ i : Bool, AEStronglyMeasurable (A i) μ
  measB : ∀ j : Bool, AEStronglyMeasurable (B j) μ
  boundA : ∀ (i : Bool) (l : Λ), |A i l| ≤ 1
  boundB : ∀ (j : Bool) (l : Λ), |B j l| ≤ 1

/-- The correlation predicted by a local hidden-variable model for settings `(i, j)`. -/

theorem quantum_chsh_eq :
    quantumCorr false false + quantumCorr false true
      + quantumCorr true false - quantumCorr true true = 2 * Real.sqrt 2 := by
  have h1 : quantumCorr false false = Real.sqrt 2 / 2 := by
    simp only [quantumCorr, aliceAngle, bobAngle]
    rw [show (0 : ℝ) - Real.pi / 4 = -(Real.pi / 4) by ring, Real.cos_neg,
      Real.cos_pi_div_four]
  have h2 : quantumCorr false true = Real.sqrt 2 / 2 := by
    simp only [quantumCorr, aliceAngle, bobAngle]
    rw [show (0 : ℝ) - -(Real.pi / 4) = Real.pi / 4 by ring, Real.cos_pi_div_four]
  have h3 : quantumCorr true false = Real.sqrt 2 / 2 := by
    simp only [quantumCorr, aliceAngle, bobAngle]
    rw [show Real.pi / 2 - Real.pi / 4 = Real.pi / 4 by ring, Real.cos_pi_div_four]
  have h4 : quantumCorr true true = -(Real.sqrt 2 / 2) := by
    simp only [quantumCorr, aliceAngle, bobAngle]
    rw [show Real.pi / 2 - -(Real.pi / 4) = Real.pi - Real.pi / 4 by ring,
      Real.cos_pi_sub, Real.cos_pi_div_four]
  rw [h1, h2, h3, h4]
  ring

/-- `2 * √2 > 2`. -/
