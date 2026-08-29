/-
# Berry Phase Quantized
Category: Frontier Physics
Target: Frontier.berry_phase_quantized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Classical

open Set MeasureTheory

namespace Frontier

/-- The **Berry connection** is modelled as a real one-form on a two-dimensional parameter
space, i.e. a map `A : ℝ × ℝ → ℝ × ℝ` whose value `A p = (A₁ p, A₂ p)` gives the components
of the form `A₁ dx + A₂ dy` at the parameter point `p`. -/
abbrev BerryConnection := ℝ × ℝ → ℝ × ℝ

/-- The **Berry curvature** of a Berry connection `A` at a parameter point `p`:
`F = ∂₁ A₂ - ∂₂ A₁`, the exterior derivative of the connection one-form. -/

theorem symGauge_curvature (k : ℝ) (p : ℝ × ℝ) : berryCurvature (symGauge k) p = k := by
  have h2 : HasFDerivAt (fun q : ℝ × ℝ => ((symGauge k) q).2)
      ((k / 2) • (ContinuousLinearMap.fst ℝ ℝ ℝ)) p :=
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt).const_mul (k / 2)
  have h1 : HasFDerivAt (fun q : ℝ × ℝ => ((symGauge k) q).1)
      ((-(k / 2)) • (ContinuousLinearMap.snd ℝ ℝ ℝ)) p :=
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt).const_mul (-(k / 2))
  rw [berryCurvature, h1.fderiv, h2.fderiv]
  simp

