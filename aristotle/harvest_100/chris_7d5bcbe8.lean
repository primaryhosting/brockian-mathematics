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

variable {α : Type*} [Fintype α]

/-- The canonical partition function `Z(β) = ∑ₓ e^{-β H(x)}` of a Hamiltonian `H`
on a finite state space. -/
noncomputable def partitionFunction (beta : ℝ) (H : α → ℝ) : ℝ :=
  ∑ x, Real.exp (-beta * H x)

/-- The Helmholtz free energy `F = -(1/β) log Z(β)`. -/
noncomputable def freeEnergy (beta : ℝ) (H : α → ℝ) : ℝ :=
  -(1 / beta) * Real.log (partitionFunction beta H)

/-- The work performed along the (deterministic, phase-space volume preserving)
protocol `Phi` that drives the system from Hamiltonian `H0` to `H1`:
`W(x) = H₁(Φ x) - H₀(x)`. -/
def work {α : Type*} (H0 H1 : α → ℝ) (Phi : α → α) (x : α) : ℝ := H1 (Phi x) - H0 x

theorem partitionFunction_pos [Nonempty α] (beta : ℝ) (H : α → ℝ) :
    0 < partitionFunction beta H := by
  refine Finset.sum_pos (fun x _ => Real.exp_pos _) ?_
  simp [Finset.univ_nonempty]

/-- **Jarzynski equality.** For a system initially in the canonical (Gibbs) state of `H0`
at inverse temperature `β ≠ 0`, driven by an arbitrary (Liouville, i.e. bijective)
protocol `Phi` to the Hamiltonian `H1`, the average of `e^{-βW}` over the initial
distribution equals `e^{-β ΔF}`, where `ΔF = F₁ - F₀` is the equilibrium free energy
difference. -/
theorem jarzynski_equality [Nonempty α] {beta : ℝ} (hbeta : beta ≠ 0)
    (H0 H1 : α → ℝ) (Phi : α ≃ α) :
    ∑ x, (Real.exp (-beta * H0 x) / partitionFunction beta H0) *
          Real.exp (-beta * work H0 H1 Phi x)
      = Real.exp (-beta * (freeEnergy beta H1 - freeEnergy beta H0)) := by
  have hZ0 : 0 < partitionFunction beta H0 := partitionFunction_pos beta H0
  have hZ1 : 0 < partitionFunction beta H1 := partitionFunction_pos beta H1
  have hlhs : ∑ x, (Real.exp (-beta * H0 x) / partitionFunction beta H0) *
        Real.exp (-beta * work H0 H1 Phi x)
      = partitionFunction beta H1 / partitionFunction beta H0 := by
    have hterm : ∀ x : α, (Real.exp (-beta * H0 x) / partitionFunction beta H0) *
        Real.exp (-beta * work H0 H1 Phi x)
        = Real.exp (-beta * H1 (Phi x)) / partitionFunction beta H0 := by
      intro x
      rw [div_mul_eq_mul_div, ← Real.exp_add, work]
      ring_nf
    rw [Finset.sum_congr rfl (fun x _ => hterm x), ← Finset.sum_div,
      Equiv.sum_comp Phi (fun y => Real.exp (-beta * H1 y)), partitionFunction]
    rfl
  rw [hlhs, freeEnergy, freeEnergy]
  have : -beta * (-(1 / beta) * Real.log (partitionFunction beta H1) -
      -(1 / beta) * Real.log (partitionFunction beta H0))
      = Real.log (partitionFunction beta H1) - Real.log (partitionFunction beta H0) := by
    field_simp
    ring
  rw [this, Real.exp_sub, Real.exp_log hZ1, Real.exp_log hZ0]

/-! ## Measure-theoretic (continuous phase space) version -/

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The partition function `Z(β) = ∫ e^{-β H(x)} dμ(x)` on a general phase space `(Ω, μ)`. -/
noncomputable def partitionFunctionOn (mu : Measure Ω) (beta : ℝ) (H : Ω → ℝ) : ℝ :=
  ∫ x, Real.exp (-beta * H x) ∂mu

/-- The Helmholtz free energy `F = -(1/β) log Z(β)` on a general phase space. -/
noncomputable def freeEnergyOn (mu : Measure Ω) (beta : ℝ) (H : Ω → ℝ) : ℝ :=
  -(1 / beta) * Real.log (partitionFunctionOn mu beta H)

/-- **Jarzynski equality, continuous phase space.** The system starts in the Gibbs state
`e^{-β H₀} dμ / Z₀` at inverse temperature `β ≠ 0` and is driven by a measure preserving
(Liouville) protocol `Φ` to the Hamiltonian `H₁`. Then `⟨e^{-βW}⟩ = e^{-β ΔF}`. -/
theorem jarzynski_equality_of_measurePreserving {mu : Measure Ω} {beta : ℝ} (hbeta : beta ≠ 0)
    (H0 H1 : Ω → ℝ) (Phi : Ω ≃ᵐ Ω) (hPhi : MeasurePreserving Phi mu mu)
    (hZ0 : 0 < partitionFunctionOn mu beta H0) (hZ1 : 0 < partitionFunctionOn mu beta H1) :
    ∫ x, (Real.exp (-beta * H0 x) / partitionFunctionOn mu beta H0) *
          Real.exp (-beta * work H0 H1 Phi x) ∂mu
      = Real.exp (-beta * (freeEnergyOn mu beta H1 - freeEnergyOn mu beta H0)) := by
  have hterm : ∀ x : Ω, (Real.exp (-beta * H0 x) / partitionFunctionOn mu beta H0) *
      Real.exp (-beta * work H0 H1 Phi x)
      = Real.exp (-beta * H1 (Phi x)) / partitionFunctionOn mu beta H0 := by
    intro x
    rw [div_mul_eq_mul_div, ← Real.exp_add, work]
    ring_nf
  have hlhs : ∫ x, (Real.exp (-beta * H0 x) / partitionFunctionOn mu beta H0) *
        Real.exp (-beta * work H0 H1 Phi x) ∂mu
      = partitionFunctionOn mu beta H1 / partitionFunctionOn mu beta H0 := by
    simp only [hterm, integral_div]
    rw [hPhi.integral_comp' (fun y => Real.exp (-beta * H1 y))]
    rfl
  rw [hlhs, freeEnergyOn, freeEnergyOn]
  have hexp : -beta * (-(1 / beta) * Real.log (partitionFunctionOn mu beta H1) -
      -(1 / beta) * Real.log (partitionFunctionOn mu beta H0))
      = Real.log (partitionFunctionOn mu beta H1) - Real.log (partitionFunctionOn mu beta H0) := by
    field_simp
    ring
  rw [hexp, Real.exp_sub, Real.exp_log hZ1, Real.exp_log hZ0]

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

