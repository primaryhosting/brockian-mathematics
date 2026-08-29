/-
# No Cloning
Category: Quantum Computing
Target: QC.no_cloning
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped TensorProduct

namespace QC

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The superposition `(a + b)/√2` of two orthonormal vectors is again a unit vector. -/

lemma inner_superposition (a b : H) (ha : ‖a‖ = 1) (hab : inner ℂ a b = (0 : ℂ)) :
    inner ℂ a (((Real.sqrt 2 : ℝ)⁻¹ : ℂ) • (a + b)) = ((Real.sqrt 2 : ℝ)⁻¹ : ℂ) := by
  rw [inner_smul_right, inner_add_right, hab, inner_self_eq_norm_sq_to_K, ha]
  norm_num

/--
**No-cloning theorem.**

Let `H` be a complex inner product space containing two orthonormal vectors `a`, `b`
(i.e. `H` has dimension at least `2`), and let `e0` be any unit "blank" state.
Then there is no unitary (linear isometry equivalence) `U` on `H ⊗ H` with
`U (ψ ⊗ e0) = ψ ⊗ ψ` for every state (unit vector) `ψ`.
-/
