import Mathlib

/-!
# Pbr Theorem
Category: Frontier Qi
Target: QI.pbr_theorem
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

set_option grind.warning false

open MeasureTheory

noncomputable section

namespace QI

/-! ## The quantum ingredients

We work with a single qubit modelled as `Fin 2 → ℂ` and a pair of qubits modelled as
`Fin 2 × Fin 2 → ℂ` (the tensor product `ℂ² ⊗ ℂ²`), equipped with the standard Hermitian
inner product `inner2`.
-/

/-- The scalar `1/√2`. -/

lemma prod_le_prod_of_le {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ₁ μ₂ : Measure α} {ν₁ ν₂ : Measure β} [SFinite ν₁] [SFinite ν₂]
    (h : μ₁ ≤ μ₂) (h' : ν₁ ≤ ν₂) : μ₁.prod ν₁ ≤ μ₂.prod ν₂ := by
  rw [Measure.le_iff]
  intro s hs
  rw [Measure.prod_apply hs, Measure.prod_apply hs]
  exact lintegral_mono' h fun x => h' _

/-! ## The PBR theorem

An *ontological model* for the two preparations `|0⟩` and `|+⟩` consists of a measurable space
`Λ` of ontic states together with a probability measure `μ i` for each preparation.  A
measurement on two systems is modelled by response functions `ξ k : Λ × Λ → ℝ≥0∞`, one for each
outcome `k`, summing pointwise to `1`.  *Preparation independence* is the statement that the
ontic state of two independently prepared systems is distributed according to the **product**
measure `(μ x₁).prod (μ x₂)`; this is exactly how the Born-rule hypothesis below is phrased.

The theorem states that under these assumptions the two distributions `μ 0` and `μ 1` have no
common part whatsoever: any measure `ρ` below both of them is zero.  In other words, the ontic
state determines the quantum state — the quantum state is ontic, not epistemic.
-/

/-- **Pusey–Barrett–Rudolph theorem.**  In any ontological model of the qubit preparations
`|0⟩` and `|+⟩` that reproduces the Born rule for the PBR entangled measurement on two systems
and satisfies preparation independence (the joint ontic distribution of two independently
prepared systems is the product of the single-system distributions), the ontic distributions of
`|0⟩` and `|+⟩` have no overlap: every measure `ρ` dominated by both of them vanishes.  Hence no
`ψ`-epistemic model is possible: the quantum state is ontic. -/
