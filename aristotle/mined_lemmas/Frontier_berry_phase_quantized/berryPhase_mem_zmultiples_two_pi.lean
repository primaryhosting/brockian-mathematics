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

theorem berryPhase_mem_zmultiples_two_pi (A : BerryConnection) (a₁ a₂ b₁ b₂ : ℝ)
    (h1 : Differentiable ℝ (fun q => (A q).1))
    (h2 : Differentiable ℝ (fun q => (A q).2))
    (Hi : IntegrableOn (berryCurvature A) (uIcc a₁ b₁ ×ˢ uIcc a₂ b₂))
    (hflux : berryFlux A a₁ a₂ b₁ b₂ ∈ AddSubgroup.zmultiples (2 * Real.pi)) :
    berryPhase A a₁ a₂ b₁ b₂ ∈ AddSubgroup.zmultiples (2 * Real.pi) := by
  rw [berryPhase_eq_berryFlux A a₁ a₂ b₁ b₂ h1 h2 Hi]
  exact hflux

/-! ### The quantum-mechanical Berry phase of a cyclic family of states -/

/-- The Berry phase `i ∮ ⟨ψ | ∂ₜ ψ⟩ dt` accumulated over the time interval `[0, T]` by a
(normalized) family of states `ψ : ℝ → ℂ` in a one-dimensional Hilbert space. -/
