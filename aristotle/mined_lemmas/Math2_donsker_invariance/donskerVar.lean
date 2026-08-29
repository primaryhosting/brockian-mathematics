/-
# Donsker Invariance
Category: Frontier Math
Target: Math2.donsker_invariance
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Donsker Invariance
Category: Frontier Math
Target: Math2.donsker_invariance
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Math2

/-- The linearly interpolated, rescaled random walk
`W_n(t) = (S_{⌊nt⌋} + (nt - ⌊nt⌋) X_{⌊nt⌋}) / √n`, where `S_m = X_0 + ⋯ + X_{m-1}`.
This is the classical Donsker polygonal process associated to the steps `X`. -/

noncomputable def donskerVar (n : ℕ) (t : ℝ) : ℝ≥0 :=
  (((⌊(n : ℝ) * t⌋₊ : ℝ) + ((n : ℝ) * t - ⌊(n : ℝ) * t⌋₊) ^ 2) / n).toNNReal

/-- `B` is a Brownian motion on the probability space `(Ω, P)`: it starts at `0`, has continuous
paths, independent increments, and `B t - B s` is centred Gaussian with variance `t - s`. -/
structure IsBrownianMotion {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (B : ℝ → Ω → ℝ) :
    Prop where
  measurable : ∀ t, Measurable (B t)
  start_zero : ∀ ω, B 0 ω = 0
  continuous_paths : ∀ ω, Continuous fun t ↦ B t ω
  gaussian_increments : ∀ s t, 0 ≤ s → s ≤ t →
    P.map (fun ω ↦ B t ω - B s ω) = gaussianReal 0 (t - s).toNNReal
  indep_increments : ∀ (k : ℕ) (u : ℕ → ℝ), Monotone u → 0 ≤ u 0 →
    iIndepFun (fun i : Fin k ↦ fun ω ↦ B (u (i + 1)) ω - B (u i) ω) P

section Lemmas

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- A centred Gaussian measure is the image of the standard Gaussian under scaling by `√v`. -/
