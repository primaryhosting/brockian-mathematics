/-
# Jarzynski Equality
Category: Frontier Phys
Target: Phys.jarzynski_equality
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Jarzynski Equality
Category: Frontier Phys
Target: Phys.jarzynski_equality
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

open Finset

variable {Ω : Type*} [Fintype Ω]

/-- The canonical partition function `Z = ∑ₓ e^{-βH(x)}` of a Hamiltonian `H`
on a finite phase space at inverse temperature `β`. -/
noncomputable def partitionFunction (β : ℝ) (H : Ω → ℝ) : ℝ :=
  ∑ x, Real.exp (-β * H x)

/-- The Helmholtz free energy `F = -(1/β) log Z`. -/
noncomputable def freeEnergy (β : ℝ) (H : Ω → ℝ) : ℝ :=
  -(Real.log (partitionFunction β H)) / β

/-- The equilibrium (Boltzmann–Gibbs) probability of a state `x`. -/
noncomputable def gibbs (β : ℝ) (H : Ω → ℝ) (x : Ω) : ℝ :=
  Real.exp (-β * H x) / partitionFunction β H

/-- The work performed along the trajectory starting at `x`, when the system evolves
under the (deterministic, phase-space volume preserving) map `φ` while the Hamiltonian
is switched from `H₀` to `H₁`. -/
def work (H₀ H₁ : Ω → ℝ) (φ : Equiv.Perm Ω) (x : Ω) : ℝ :=
  H₁ (φ x) - H₀ x

theorem partitionFunction_pos [Nonempty Ω] (β : ℝ) (H : Ω → ℝ) :
    0 < partitionFunction β H := by
  refine Finset.sum_pos (fun x _ => Real.exp_pos _) ?_
  simp [Finset.univ_nonempty]

/-- **Jarzynski equality.**  For a system prepared in thermal equilibrium with respect to
`H₀` at inverse temperature `β`, and driven by a deterministic, measure-preserving
(here: bijective) evolution `φ` to the final Hamiltonian `H₁`, the average of `e^{-βW}`
over the initial equilibrium ensemble equals `e^{-βΔF}`, where `ΔF = F₁ - F₀` is the
equilibrium free-energy difference. -/
theorem jarzynski_equality [Nonempty Ω] (β : ℝ) (hβ : β ≠ 0)
    (H₀ H₁ : Ω → ℝ) (φ : Equiv.Perm Ω) :
    ∑ x, gibbs β H₀ x * Real.exp (-β * work H₀ H₁ φ x)
      = Real.exp (-β * (freeEnergy β H₁ - freeEnergy β H₀)) := by
  have hZ₀ : 0 < partitionFunction β H₀ := partitionFunction_pos β H₀
  have hZ₁ : 0 < partitionFunction β H₁ := partitionFunction_pos β H₁
  have hlhs : ∑ x, gibbs β H₀ x * Real.exp (-β * work H₀ H₁ φ x)
      = partitionFunction β H₁ / partitionFunction β H₀ := by
    rw [partitionFunction, Finset.sum_div]
    rw [← Equiv.sum_comp φ (fun y => Real.exp (-β * H₁ y) / partitionFunction β H₀)]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [gibbs, work, div_mul_eq_mul_div, ← Real.exp_add]
    ring_nf
  rw [hlhs, freeEnergy, freeEnergy]
  have : -β * (-(Real.log (partitionFunction β H₁)) / β
      - -(Real.log (partitionFunction β H₀)) / β)
      = Real.log (partitionFunction β H₁) - Real.log (partitionFunction β H₀) := by
    field_simp
    ring
  rw [this, Real.exp_sub, Real.exp_log hZ₁, Real.exp_log hZ₀]

/-- The Boltzmann–Gibbs weights form a probability distribution. -/
theorem sum_gibbs [Nonempty Ω] (β : ℝ) (H : Ω → ℝ) : ∑ x, gibbs β H x = 1 := by
  simp only [gibbs]
  rw [← Finset.sum_div, ← partitionFunction]
  exact div_self (partitionFunction_pos β H).ne'

theorem gibbs_nonneg (β : ℝ) (H : Ω → ℝ) (x : Ω) : 0 ≤ gibbs β H x :=
  div_nonneg (Real.exp_pos _).le (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le)

/-- **Second law of thermodynamics** as a corollary of the Jarzynski equality:
the average work done on the system is at least the free-energy difference,
`⟨W⟩ ≥ ΔF`.  (Obtained from `⟨e^{-βW}⟩ = e^{-βΔF}` by Jensen's inequality.) -/
theorem average_work_ge_freeEnergy_diff [Nonempty Ω] (β : ℝ) (hβ : 0 < β)
    (H₀ H₁ : Ω → ℝ) (φ : Equiv.Perm Ω) :
    freeEnergy β H₁ - freeEnergy β H₀
      ≤ ∑ x, gibbs β H₀ x * work H₀ H₁ φ x := by
  have hjensen : Real.exp (∑ x, gibbs β H₀ x * (-β * work H₀ H₁ φ x))
      ≤ ∑ x, gibbs β H₀ x * Real.exp (-β * work H₀ H₁ φ x) := by
    simpa [smul_eq_mul] using
      convexOn_exp.map_sum_le (t := (Finset.univ : Finset Ω)) (w := gibbs β H₀)
        (p := fun x => -β * work H₀ H₁ φ x)
        (fun i _ => gibbs_nonneg β H₀ i) (sum_gibbs β H₀) (fun i _ => Set.mem_univ _)
  rw [jarzynski_equality β hβ.ne' H₀ H₁ φ] at hjensen
  have hsum : ∑ x, gibbs β H₀ x * (-β * work H₀ H₁ φ x)
      = -β * ∑ x, gibbs β H₀ x * work H₀ H₁ φ x := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [hsum] at hjensen
  have := Real.exp_le_exp.mp hjensen
  nlinarith [this]

section Continuous

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Partition function on a general (continuous) phase space with reference measure `μ`
(e.g. Liouville measure): `Z = ∫ e^{-βH} dμ`. -/
noncomputable def partitionFunctionOn (μ : Measure Ω) (β : ℝ) (H : Ω → ℝ) : ℝ :=
  ∫ x, Real.exp (-β * H x) ∂μ

/-- Free energy on a general phase space: `F = -(1/β) log Z`. -/
noncomputable def freeEnergyOn (μ : Measure Ω) (β : ℝ) (H : Ω → ℝ) : ℝ :=
  -(Real.log (partitionFunctionOn μ β H)) / β

/-- Equilibrium (Boltzmann–Gibbs) density with respect to `μ`. -/
noncomputable def gibbsDensity (μ : Measure Ω) (β : ℝ) (H : Ω → ℝ) (x : Ω) : ℝ :=
  Real.exp (-β * H x) / partitionFunctionOn μ β H

/-- **Jarzynski equality on a general phase space.**  For a system prepared in thermal
equilibrium with respect to `H₀` and driven by a deterministic, measure-preserving
invertible evolution `φ` (Liouville's theorem), the equilibrium average of `e^{-βW}`
with `W(x) = H₁(φ x) - H₀(x)` equals `e^{-βΔF}`. -/
theorem jarzynski_equality_of_measurePreserving (μ : Measure Ω) (β : ℝ) (hβ : β ≠ 0)
    (H₀ H₁ : Ω → ℝ) (φ : Ω ≃ᵐ Ω) (hφ : MeasurePreserving φ μ μ)
    (hZ₀ : 0 < partitionFunctionOn μ β H₀) (hZ₁ : 0 < partitionFunctionOn μ β H₁) :
    ∫ x, gibbsDensity μ β H₀ x * Real.exp (-β * (H₁ (φ x) - H₀ x)) ∂μ
      = Real.exp (-β * (freeEnergyOn μ β H₁ - freeEnergyOn μ β H₀)) := by
  have hpt : ∀ x, gibbsDensity μ β H₀ x * Real.exp (-β * (H₁ (φ x) - H₀ x))
      = Real.exp (-β * H₁ (φ x)) / partitionFunctionOn μ β H₀ := by
    intro x
    rw [gibbsDensity, div_mul_eq_mul_div, ← Real.exp_add]
    ring_nf
  calc ∫ x, gibbsDensity μ β H₀ x * Real.exp (-β * (H₁ (φ x) - H₀ x)) ∂μ
      = ∫ x, Real.exp (-β * H₁ (φ x)) / partitionFunctionOn μ β H₀ ∂μ := by
        exact integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = (∫ x, Real.exp (-β * H₁ (φ x)) ∂μ) / partitionFunctionOn μ β H₀ := by
        rw [integral_div]
    _ = partitionFunctionOn μ β H₁ / partitionFunctionOn μ β H₀ := by
        rw [hφ.integral_comp' (fun y => Real.exp (-β * H₁ y))]
        rfl
    _ = Real.exp (-β * (freeEnergyOn μ β H₁ - freeEnergyOn μ β H₀)) := by
        rw [freeEnergyOn, freeEnergyOn]
        have h : -β * (-(Real.log (partitionFunctionOn μ β H₁)) / β
            - -(Real.log (partitionFunctionOn μ β H₀)) / β)
            = Real.log (partitionFunctionOn μ β H₁)
              - Real.log (partitionFunctionOn μ β H₀) := by
          field_simp
          ring
        rw [h, Real.exp_sub, Real.exp_log hZ₁, Real.exp_log hZ₀]

end Continuous

end Phys

import Mathlib

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

