import Mathlib

/-!
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

open Matrix
open scoped ComplexOrder MatrixOrder

variable {N M : ℕ}

/-- A linear map between matrix algebras `M_N(ℂ) → M_M(ℂ)`. -/
abbrev MatMap (N M : ℕ) : Type :=
  Matrix (Fin N) (Fin N) ℂ →ₗ[ℂ] Matrix (Fin M) (Fin M) ℂ

/-- The amplification `id_{M_k} ⊗ Φ`, acting on `k × k` block matrices with blocks in
`M_N(ℂ)` by applying `Φ` to each block. -/

lemma choiMatrix_id : choiMatrix (LinearMap.id : MatMap N N) = omegaMat N := by
  ext p q
  simp only [choiMatrix, omegaMat, Matrix.of_apply, LinearMap.id_coe, id_eq,
    Matrix.single_apply]
  by_cases h1 : p.1 = p.2 <;> by_cases h2 : q.1 = q.2 <;> simp [h1, h2]

/-- The identity map is completely positive. -/
