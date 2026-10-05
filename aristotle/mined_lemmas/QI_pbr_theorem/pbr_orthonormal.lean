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

theorem pbr_orthonormal (j k : Fin 2 × Fin 2) :
    inner2 (pbrVec j) (pbrVec k) = if j = k then 1 else 0 := by
  obtain ⟨j1, j2⟩ := j
  obtain ⟨k1, k2⟩ := k
  fin_cases j1 <;> fin_cases j2 <;> fin_cases k1 <;> fin_cases k2 <;>
    simp [inner2_eq, pbrVec, tensor, ket0, ket1, ketPlus, ketMinus, conj_invSqrtTwo,
      Prod.ext_iff] <;>
    ring_nf <;>
    try (simp [invSqrtTwo_sq, invSqrtTwo_pow4, invSqrtTwo_pow6]; try ring_nf)

/-- The key quantum fact behind PBR: for each of the four product preparations
`|ψ_{x₁}⟩ ⊗ |ψ_{x₂}⟩` (with `ψ₀ = |0⟩`, `ψ₁ = |+⟩`) the outcome labelled by `(x₁, x₂)` has
Born probability zero. -/
