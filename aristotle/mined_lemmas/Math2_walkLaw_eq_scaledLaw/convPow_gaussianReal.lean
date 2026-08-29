import RequestProject.CLT

/-!
# Convergence of the rescaled walk against smooth test functions

`Math2.walkLaw μ n t` is the law of `S_{⌊n t⌋} / √n`, where `S` is a random walk with step
distribution `μ`.  Here we prove that, for a centered step distribution with unit variance and
finite third absolute moment, the integrals of smooth test functions against `walkLaw μ n t`
converge to the corresponding integrals against the centered Gaussian law of variance `t`, which
is the law of Brownian motion at time `t`.
-/

namespace Math2

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

/-- The law of `S_p / √n`, the sum of `p` i.i.d. steps with law `μ`, rescaled by `1/√n`. -/

theorem convPow_gaussianReal (v : ℝ≥0) (n : ℕ) :
    convPow (gaussianReal 0 v) n = gaussianReal 0 (n • v) := by
  induction n with
  | zero => simp [gaussianReal_zero_var]
  | succ n ih =>
      rw [convPow_succ, ih, gaussianReal_conv_gaussianReal]
      congr 1
      ring

end Math2

/-
/-!
# Donsker Invariance
Category: Frontier Math
Target: Math2.donsker_invariance
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

import Mathlib
import RequestProject.Walk
import RequestProject.Weak

/-!
# Donsker Invariance
Category: Frontier Math
Target: Math2.donsker_invariance
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

set_option grind.warning false

namespace Math2

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal BoundedContinuousFunction

section Donsker

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : ℕ → Ω → ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ]

/-- The rescaled random walk `S_{⌊n t⌋} / √n` associated with the step sequence `X`. -/
