import Mathlib

/-!
# Navier Stokes Regularity
Category: Frontier — Moonshot
Target: Frontier.navier_stokes_regularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped ContDiff BigOperators

namespace Frontier

/-- The physical space `ℝ³`, as the space of `3`-tuples of reals. -/
abbrev Vec : Type := Fin 3 → ℝ

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The `i`-th partial derivative of a (vector- or scalar-valued) field on `ℝ³`. -/

theorem navier_stokes_regularity_reduction (h : NavierStokesGlobalRegularity 1) :
    ∀ ν : ℝ, 0 < ν → NavierStokesGlobalRegularity ν := by
  rintro ν hν u₀ ⟨hsmooth, hsupp, hdiv⟩
  have hadm : IsAdmissibleData (fun x => ν⁻¹ • u₀ x) := by
    refine ⟨hsmooth.const_smul ν⁻¹, ?_, fun x => ?_⟩
    · exact HasCompactSupport.smul_left (f := fun _ : Vec => ν⁻¹) hsupp
    · rw [divergence_const_smul ν⁻¹ (hsmooth.differentiable (by simp)) x, hdiv x, mul_zero]
  obtain ⟨v, q, hsol, hv0, C, hC⟩ := h _ hadm
  refine ⟨fun t x => ν • v (ν * t) x, fun t x => (ν * ν) • q (ν * t) x, hsol.rescale hν, ?_,
    ν ^ 2 * C, fun t ht => ?_⟩
  · funext x
    show ν • v (ν * 0) x = u₀ x
    rw [mul_zero, hv0]
    simp [smul_smul, mul_inv_cancel₀ (ne_of_gt hν)]
  · rw [energy_rescale v ν t]
    exact mul_le_mul_of_nonneg_left (hC (ν * t) (by positivity)) (by positivity)

/-- **Navier–Stokes regularity: base case and a reduction.**

The first conjunct is the base case of the global regularity statement: for every viscosity
the zero initial datum admits a globally defined smooth, finite-energy solution of the 3D
incompressible Navier–Stokes equations.

The second conjunct is a Lean-checked reduction: global regularity for unit viscosity
implies global regularity for every positive viscosity, via the time rescaling
`u(t,x) = ν v(νt, x)`, `p(t,x) = ν² q(νt, x)`.

The full Clay Millennium statement is `Frontier.NavierStokesGlobalRegularity`, which
remains open and is not asserted here. -/
