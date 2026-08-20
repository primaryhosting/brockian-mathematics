/-
# No Cloning
Category: Quantum Computing
Target: QC.no_cloning
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QC

open scoped TensorProduct

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **Key lemma.** If a unitary `U` on `H ⊗ H` clones every unit vector against the
"blank" unit vector `e₀`, then for any two unit vectors `u`, `v` the overlap
`⟪u, v⟫` satisfies `⟪u, v⟫ = ⟪u, v⟫ ^ 2`, since unitaries preserve inner products. -/

theorem inner_sq_eq_inner_of_cloner
    (e0 : H) (he0 : ‖e0‖ = 1)
    (U : (H ⊗[ℂ] H) ≃ₗᵢ[ℂ] (H ⊗[ℂ] H))
    (hU : ∀ u : H, ‖u‖ = 1 → U (u ⊗ₜ[ℂ] e0) = u ⊗ₜ[ℂ] u)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    inner ℂ u v = (inner ℂ u v : ℂ) ^ 2 := by
  have he0' : (inner ℂ e0 e0 : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, he0]
    norm_num
  have h1 : (inner ℂ (U (u ⊗ₜ[ℂ] e0)) (U (v ⊗ₜ[ℂ] e0)) : ℂ)
      = inner ℂ (u ⊗ₜ[ℂ] e0) (v ⊗ₜ[ℂ] e0) := U.inner_map_map _ _
  rw [hU u hu, hU v hv, TensorProduct.inner_tmul, TensorProduct.inner_tmul, he0'] at h1
  rw [pow_two, h1, mul_one]

/-- **No-cloning theorem.** If the state space `H` contains two orthonormal vectors
`e0`, `e1` (i.e. `H` has dimension at least two), then there is no unitary `U` on
`H ⊗ H` that clones every unit vector against the blank state `e0`, i.e. satisfying
`U (u ⊗ e0) = u ⊗ u` for all unit vectors `u`. -/
