import Mathlib
/-!
# No Cloning
Category: Quantum Computing
Target: QC.no_cloning
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped TensorProduct

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QC

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **Key lemma.** If a unitary `U` on `H ⊗ H` clones every unit vector against the fixed
unit "blank" state `e₀`, i.e. `U (x ⊗ e₀) = x ⊗ x`, then the inner product of any two unit
vectors is idempotent: `⟪x, y⟫ * ⟪x, y⟫ = ⟪x, y⟫`.

Indeed, unitarity gives `⟪x, y⟫ = ⟪x ⊗ e₀, y ⊗ e₀⟫ = ⟪x ⊗ x, y ⊗ y⟫ = ⟪x, y⟫²`. -/

lemma inner_mul_self_eq_inner_of_clones
    (e0 : H) (he0 : ‖e0‖ = 1)
    (U : (H ⊗[ℂ] H) ≃ₗᵢ[ℂ] (H ⊗[ℂ] H))
    (hU : ∀ x : H, ‖x‖ = 1 → U (x ⊗ₜ[ℂ] e0) = x ⊗ₜ[ℂ] x)
    (x y : H) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    (inner ℂ x y) * (inner ℂ x y) = inner ℂ x y := by
  have h := U.inner_map_map (x ⊗ₜ[ℂ] e0) (y ⊗ₜ[ℂ] e0)
  rw [hU x hx, hU y hy] at h
  simp [TensorProduct.inner_tmul, inner_self_eq_norm_sq_to_K, he0] at h
  simpa using h

/-- In a complex inner product space of rank at least two there is an orthonormal pair. -/
