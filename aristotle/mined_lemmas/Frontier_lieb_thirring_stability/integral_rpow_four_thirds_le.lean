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

theorem integral_rpow_four_thirds_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {ρ : α → ℝ} (hρ0 : 0 ≤ᵐ[μ] ρ) (hρm : AEStronglyMeasurable ρ μ)
    (hρ1 : Integrable ρ μ) (hρ53 : Integrable (fun x => ρ x ^ (5 / 3 : ℝ)) μ) :
    ∫ x, ρ x ^ (4 / 3 : ℝ) ∂μ
      ≤ (∫ x, ρ x ^ (5 / 3 : ℝ) ∂μ) ^ (1 / 2 : ℝ) * (∫ x, ρ x ∂μ) ^ (1 / 2 : ℝ) := by
  have hmf : AEStronglyMeasurable (fun x => ρ x ^ (5 / 6 : ℝ)) μ :=
    (hρm.aemeasurable.pow_const (5 / 6 : ℝ)).aestronglyMeasurable
  have hmg : AEStronglyMeasurable (fun x => ρ x ^ (1 / 2 : ℝ)) μ :=
    (hρm.aemeasurable.pow_const (1 / 2 : ℝ)).aestronglyMeasurable
  have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) := by simp
  have hf : MemLp (fun x => ρ x ^ (5 / 6 : ℝ)) (ENNReal.ofReal (2 : ℝ)) μ := by
    rw [← h2, memLp_two_iff_integrable_sq hmf]
    apply hρ53.congr
    filter_upwards [hρ0] with x hx
    rw [← Real.rpow_natCast (ρ x ^ (5 / 6 : ℝ)) 2, ← Real.rpow_mul hx]
    norm_num
  have hg : MemLp (fun x => ρ x ^ (1 / 2 : ℝ)) (ENNReal.ofReal (2 : ℝ)) μ := by
    rw [← h2, memLp_two_iff_integrable_sq hmg]
    apply hρ1.congr
    filter_upwards [hρ0] with x hx
    rw [← Real.rpow_natCast (ρ x ^ (1 / 2 : ℝ)) 2, ← Real.rpow_mul hx]
    norm_num
  have key := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (f := fun x => ρ x ^ (5 / 6 : ℝ)) (g := fun x => ρ x ^ (1 / 2 : ℝ))
    (by filter_upwards [hρ0] with x hx using Real.rpow_nonneg hx _)
    (by filter_upwards [hρ0] with x hx using Real.rpow_nonneg hx _) hf hg
  have e1 : ∫ x, ρ x ^ (5 / 6 : ℝ) * ρ x ^ (1 / 2 : ℝ) ∂μ = ∫ x, ρ x ^ (4 / 3 : ℝ) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hρ0] with x hx
    rw [← Real.rpow_add' hx (by norm_num)]
    norm_num
  have e2 : ∫ x, (ρ x ^ (5 / 6 : ℝ)) ^ (2 : ℝ) ∂μ = ∫ x, ρ x ^ (5 / 3 : ℝ) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hρ0] with x hx
    rw [← Real.rpow_mul hx]; norm_num
  have e3 : ∫ x, (ρ x ^ (1 / 2 : ℝ)) ^ (2 : ℝ) ∂μ = ∫ x, ρ x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hρ0] with x hx
    rw [← Real.rpow_mul hx]; norm_num
  rw [e1, e2, e3] at key
  simpa using key

/-- **Completing the square.** The Thomas–Fermi type minimization
`K t - A √t √n ≥ - A ^ 2 n / (4 K)`. -/
