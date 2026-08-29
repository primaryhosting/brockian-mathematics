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

noncomputable def stateBerryPhase (psi : ℝ → ℂ) (T : ℝ) : ℂ :=
  Complex.I * ∫ t in (0 : ℝ)..T, (starRingEnd ℂ) (psi t) * deriv psi t

/-- **The Berry phase of a winding family of states is quantized.**  For the cyclic family
`ψₙ(t) = exp(i n t)` of unit vectors, which returns to itself at `t = 2π`, the Berry phase is
`-2π n`, an integer multiple of `2π`. -/
