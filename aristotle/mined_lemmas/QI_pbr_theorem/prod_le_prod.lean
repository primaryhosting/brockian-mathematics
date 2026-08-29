/-
# Pbr Theorem
Category: Frontier Qi
Target: QI.pbr_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace QI

open MeasureTheory MeasureTheory.Measure Complex

noncomputable section

/-! ## The quantum input: the Pusey–Barrett–Rudolph measurement on two qubits -/

/-- The real number `1/√2`, viewed as a complex amplitude. -/

lemma prod_le_prod {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ μ' : Measure α} {ν ν' : Measure β} [SFinite ν] [SFinite ν']
    (hμ : μ ≤ μ') (hν : ν ≤ ν') : μ.prod ν ≤ μ'.prod ν' := by
  rw [Measure.le_iff]
  intro s hs
  rw [Measure.prod_apply hs, Measure.prod_apply hs]
  calc ∫⁻ x, ν (Prod.mk x ⁻¹' s) ∂μ ≤ ∫⁻ x, ν' (Prod.mk x ⁻¹' s) ∂μ :=
        lintegral_mono fun _ => Measure.le_iff'.mp hν _
    _ ≤ ∫⁻ x, ν' (Prod.mk x ⁻¹' s) ∂μ' := lintegral_mono' hμ le_rfl

/-! ## The PBR theorem -/

/-- **Pusey–Barrett–Rudolph theorem.**

Consider an ontological (hidden-variable) model on a measurable space `Λ` of ontic states, in
which the two qubit preparations `|ψ₀⟩ = |0⟩` and `|ψ₁⟩ = |+⟩` are represented by probability
measures `μ 0` and `μ 1` on `Λ`.  Assume:

* *preparation independence*: the ontic state of two independently prepared systems is
  distributed according to the product measure `(μ a).prod (μ b)`;
* the model reproduces the Born rule for the entangled PBR measurement `pbrVec` on the two-qubit
  system: measurable response functions `ξ k : Λ × Λ → ℝ≥0∞` with `∑ k, ξ k x = 1` for every
  ontic state `x`, whose averages against the prepared distribution give the Born probabilities
  `|⟨pbrVec k, ψ_a ⊗ ψ_b⟩|²`.

Then the two quantum states are *ontologically distinct*: the measures `μ 0` and `μ 1` are
mutually singular, so no ontic state is compatible with both preparations.  In other words, the
quantum state is an ontic (physical) property of the system, not a merely epistemic one. -/
