import Mathlib

/-!
# Jarzynski Equality
Category: Frontier Phys
Target: Phys.jarzynski_equality
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Phys

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The (classical) partition function of a Hamiltonian `H` at inverse temperature `β`,
computed against the phase-space (Liouville) measure `μ`:
`Z = ∫ exp (-β * H x) dμ x`. -/
noncomputable def partitionFunction (μ : Measure Ω) (β : ℝ) (H : Ω → ℝ) : ℝ :=
  ∫ x, Real.exp (-β * H x) ∂μ

/-- The Helmholtz free energy `F = -(1/β) log Z`. -/
noncomputable def freeEnergy (μ : Measure Ω) (β : ℝ) (H : Ω → ℝ) : ℝ :=
  -(1 / β) * Real.log (partitionFunction μ β H)

/-- The canonical (Gibbs) equilibrium density with respect to `μ`,
`p(x) = exp (-β * H x) / Z`. -/
noncomputable def gibbsDensity (μ : Measure Ω) (β : ℝ) (H : Ω → ℝ) (x : Ω) : ℝ :=
  Real.exp (-β * H x) / partitionFunction μ β H

/-- The work performed on the system along the protocol that drives the Hamiltonian from
`H₀` to `H₁`, where `Φ` is the (Liouville) evolution map of the phase point during the
protocol: `W(x) = H₁ (Φ x) - H₀ x`. -/
def work (H₀ H₁ : Ω → ℝ) (Φ : Ω → Ω) (x : Ω) : ℝ := H₁ (Φ x) - H₀ x

omit [MeasurableSpace Ω] in
/-- Elementary identity: the Boltzmann weight of the initial state times `exp (-β W)`
is the Boltzmann weight of the final state. -/
lemma exp_neg_beta_work_mul_boltzmann (β : ℝ) (H₀ H₁ : Ω → ℝ) (Φ : Ω → Ω) (x : Ω) :
    Real.exp (-β * work H₀ H₁ Φ x) * Real.exp (-β * H₀ x) = Real.exp (-β * H₁ (Φ x)) := by
  rw [← Real.exp_add]
  congr 1
  simp [work]
  ring

/-- Liouville's theorem (as a hypothesis on `Φ`) gives invariance of the final partition
function under the evolution map. -/
lemma integral_boltzmann_comp_of_measurePreserving
    {μ : Measure Ω} (β : ℝ) (H₁ : Ω → ℝ) (Φ : Ω ≃ᵐ Ω) (hΦ : MeasurePreserving Φ μ μ) :
    ∫ x, Real.exp (-β * H₁ (Φ x)) ∂μ = partitionFunction μ β H₁ :=
  hΦ.integral_comp Φ.measurableEmbedding (fun y => Real.exp (-β * H₁ y))

/-- The average of `exp (-β W)` over the initial canonical ensemble is the ratio of
partition functions `Z₁ / Z₀`. -/
lemma integral_exp_neg_beta_work
    {μ : Measure Ω} (β : ℝ) (H₀ H₁ : Ω → ℝ) (Φ : Ω ≃ᵐ Ω) (hΦ : MeasurePreserving Φ μ μ) :
    ∫ x, Real.exp (-β * work H₀ H₁ Φ x) * gibbsDensity μ β H₀ x ∂μ
      = partitionFunction μ β H₁ / partitionFunction μ β H₀ := by
  have h : ∀ x : Ω, Real.exp (-β * work H₀ H₁ Φ x) * gibbsDensity μ β H₀ x
      = Real.exp (-β * H₁ (Φ x)) / partitionFunction μ β H₀ := by
    intro x
    rw [gibbsDensity, mul_div_assoc', exp_neg_beta_work_mul_boltzmann]
  simp only [h]
  rw [integral_div, integral_boltzmann_comp_of_measurePreserving β H₁ Φ hΦ]

/-- **The Jarzynski equality.**

A classical system is prepared in canonical equilibrium at inverse temperature `β` with
Hamiltonian `H₀`, i.e. with Gibbs density `exp (-β H₀ x) / Z₀` relative to the phase-space
measure `μ`.  It is then driven arbitrarily far from equilibrium by a protocol whose net
effect on phase points is the (Liouville, i.e. measure-preserving) map `Φ`, ending with
Hamiltonian `H₁`.  The work done in a realization starting at `x` is
`W(x) = H₁ (Φ x) - H₀ x`.

Then the nonequilibrium work average of `exp (-β W)` equals `exp (-β ΔF)`, where
`ΔF = F₁ - F₀` is the *equilibrium* free-energy difference between the two Hamiltonians:

`⟨e^{-βW}⟩ = e^{-βΔF}`. -/
theorem jarzynski_equality
    {μ : Measure Ω} {β : ℝ} (hβ : β ≠ 0) {H₀ H₁ : Ω → ℝ} (Φ : Ω ≃ᵐ Ω)
    (hΦ : MeasurePreserving Φ μ μ)
    (hZ₀ : 0 < partitionFunction μ β H₀) (hZ₁ : 0 < partitionFunction μ β H₁) :
    ∫ x, Real.exp (-β * work H₀ H₁ Φ x) * gibbsDensity μ β H₀ x ∂μ
      = Real.exp (-β * (freeEnergy μ β H₁ - freeEnergy μ β H₀)) := by
  rw [integral_exp_neg_beta_work β H₀ H₁ Φ hΦ]
  have hexp : -β * (freeEnergy μ β H₁ - freeEnergy μ β H₀)
      = Real.log (partitionFunction μ β H₁) - Real.log (partitionFunction μ β H₀) := by
    simp only [freeEnergy]
    field_simp
    ring
  rw [hexp, Real.exp_sub, Real.exp_log hZ₁, Real.exp_log hZ₀]

end Phys

