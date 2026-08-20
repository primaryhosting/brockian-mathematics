/-
/-!
# No Cloning
Category: Quantum Computing
Target: QC.no_cloning
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/
-- (The header above is reproduced verbatim as the module docstring below; Lean requires
-- `import` commands to precede any docstring command.)

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

namespace QC

/-- The state space of a single qubit, `H = ℂ²` with its standard inner product. -/
abbrev Qubit : Type := EuclideanSpace ℂ (Fin 2)

/-- The state space of a pair of qubits, `H ⊗ H ≅ ℂ² ⊗ ℂ² ≅ ℂ^(2×2)`. -/
abbrev TwoQubit : Type := EuclideanSpace ℂ (Fin 2 × Fin 2)

/-- The tensor (Kronecker) product of two qubit states: `(u ⊗ v) (i, j) = u i * v j`. -/

theorem no_cloning_general {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (ten : H → H → E)
    (hten : ∀ a b c d, inner ℂ (ten a b) (ten c d) = inner ℂ a c * inner ℂ b d)
    (e0 u v : H) (he0 : ‖e0‖ = 1) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (h0 : inner ℂ u v ≠ 0) (h1 : inner ℂ u v ≠ 1) :
    ¬ ∃ U : E ≃ₗᵢ[ℂ] E, ∀ psi : H, ‖psi‖ = 1 → U (ten psi e0) = ten psi psi := by
  rintro ⟨U, hU⟩
  have hself : inner ℂ e0 e0 = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, he0]; norm_num
  have key : (inner ℂ u v : ℂ) * inner ℂ u v = 1 * inner ℂ u v := by
    have h := U.inner_map_map (ten u e0) (ten v e0)
    rw [hU u hu, hU v hv, hten, hten, hself, mul_one] at h
    rw [one_mul]; exact h
  exact h1 (mul_right_cancel₀ h0 key)

