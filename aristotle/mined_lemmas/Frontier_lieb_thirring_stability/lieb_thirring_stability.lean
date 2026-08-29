/-
# Lieb Thirring Stability
Category: Frontier Physics
Target: Frontier.lieb_thirring_stability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is a plain block comment: in Lean 4 a module docstring `/-! ... -/`
-- may not precede the `import` lines; it is repeated as a docstring below.)

import Mathlib

/-!
# Lieb Thirring Stability
Category: Frontier Physics
Target: Frontier.lieb_thirring_stability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ENNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.piBinderTypes true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true

set_option grind.warning false

namespace Frontier

open MeasureTheory

/-!
## Stability of matter from the Lieb–Thirring kinetic energy inequality

The Lieb–Thirring inequality states that for an antisymmetric normalized `N`-fermion wave
function `Ψ` in three dimensions, with one-body density `ρ_Ψ`, the kinetic energy obeys

  `T(Ψ) ≥ K ∫ ρ_Ψ ^ (5/3)`

for a universal constant `K > 0`.  Together with an electrostatic (Thomas–Fermi type) lower
bound for the Coulomb interaction of the electrons with `M` nuclei,

  `W(Ψ) ≥ - A ∫ ρ_Ψ ^ (4/3) - B * M`,

it implies *stability of matter of the second kind*: the total energy is bounded below by a
constant times the number of particles,

  `T(Ψ) + W(Ψ) ≥ - (A ^ 2 / (4 K)) * N - B * M`,

where `N = ∫ ρ_Ψ` is the number of electrons.

This file formalizes that implication as a Lean-checked reduction: the two physical input
bounds are taken as hypotheses (they are the analytic inputs of the theory), and the linear
lower bound on the energy is derived.  The mathematical content of the reduction is the
Cauchy–Schwarz interpolation `∫ ρ^(4/3) ≤ (∫ ρ^(5/3))^(1/2) (∫ ρ)^(1/2)` followed by
completing the square, which is exactly the argument of Lieb and Thirring.
-/

/-- **Interpolation step.** For a nonnegative density `ρ` with `ρ` and `ρ ^ (5/3)` integrable,
Cauchy–Schwarz (Hölder with exponents `2, 2` applied to `ρ ^ (5/6) · ρ ^ (1/2)`) gives
`∫ ρ ^ (4/3) ≤ (∫ ρ ^ (5/3)) ^ (1/2) * (∫ ρ) ^ (1/2)`. -/

theorem lieb_thirring_stability {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {ρ : α → ℝ} (hρ0 : 0 ≤ᵐ[μ] ρ) (hρm : AEStronglyMeasurable ρ μ)
    (hρ1 : Integrable ρ μ) (hρ53 : Integrable (fun x => ρ x ^ (5 / 3 : ℝ)) μ)
    {N M K A B T W : ℝ} (hK : 0 < K) (hA : 0 ≤ A)
    (hN : ∫ x, ρ x ∂μ = N)
    (hT : K * ∫ x, ρ x ^ (5 / 3 : ℝ) ∂μ ≤ T)
    (hW : -(A * ∫ x, ρ x ^ (4 / 3 : ℝ) ∂μ) - B * M ≤ W) :
    -(A ^ 2 / (4 * K)) * N - B * M ≤ T + W := by
  set t : ℝ := ∫ x, ρ x ^ (5 / 3 : ℝ) ∂μ with ht
  have ht0 : 0 ≤ t := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [hρ0] with x hx using Real.rpow_nonneg hx _
  have hN0 : 0 ≤ N := by
    rw [← hN]
    exact integral_nonneg_of_ae hρ0
  have hCS : ∫ x, ρ x ^ (4 / 3 : ℝ) ∂μ ≤ t ^ (1 / 2 : ℝ) * N ^ (1 / 2 : ℝ) := by
    have := integral_rpow_four_thirds_le hρ0 hρm hρ1 hρ53
    rwa [hN] at this
  have hquad := thomas_fermi_quadratic_bound (K := K) (A := A) (t := t) (n := N) hK ht0 hN0
  have hWle : -(A * (t ^ (1 / 2 : ℝ) * N ^ (1 / 2 : ℝ))) - B * M ≤ W := by
    refine le_trans ?_ hW
    have : A * ∫ x, ρ x ^ (4 / 3 : ℝ) ∂μ ≤ A * (t ^ (1 / 2 : ℝ) * N ^ (1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hCS hA
    linarith
  linarith

end Frontier

