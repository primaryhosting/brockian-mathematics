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

lemma krausAmpl_conj_apply {k : ℕ} (V : Matrix (Fin M) (Fin N) ℂ)
    (A : Matrix (Fin k × Fin N) (Fin k × Fin N) ℂ) (p q : Fin k × Fin M) :
    (krausAmpl k V * A * (krausAmpl k V)ᴴ) p q
      = (V * (Matrix.of fun i j => A (p.1, i) (q.1, j)) * Vᴴ) p.2 q.2 := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, krausAmpl, Matrix.of_apply,
    Fintype.sum_prod_type, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp only [apply_ite (star : ℂ → ℂ), star_zero, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  refine Finset.sum_congr rfl fun _ _ => ?_
  congr 1
  rw [Finset.sum_comm]
  simp

