import Mathlib

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

namespace Chem

/-- A primitive 16-th root of unity. -/

lemma adj_mul_dft :
    C16adj * dftMat = dftMat * Matrix.diagonal (fun k => ((huckelEigen k : ℝ) : ℂ)) := by
  ext i k
  rw [adjMatrix_mul_apply, Matrix.mul_apply]
  rw [Finset.sum_eq_single k (fun b _ hb => by rw [Matrix.diagonal_apply_ne _ hb, mul_zero])
    (by simp)]
  simp only [dftMat, Matrix.diagonal_apply_eq, huckelEigen]
  have hs : zeta ^ (((i + 1 : Fin 16) : ℕ) * (k : ℕ)) = zeta ^ ((i : ℕ) * k) * zeta ^ (k : ℕ) := by
    rw [← pow_add]
    apply zeta_pow_congr
    rw [succ_val]
    conv_lhs => rw [Nat.mul_mod, Nat.mod_mod]
    rw [← Nat.mul_mod]
    congr 1
    ring
  have hp : zeta ^ (((i - 1 : Fin 16) : ℕ) * (k : ℕ))
      = zeta ^ ((i : ℕ) * k) * zeta ^ (15 * (k : ℕ)) := by
    rw [← pow_add]
    apply zeta_pow_congr
    rw [pred_val]
    conv_lhs => rw [Nat.mul_mod, Nat.mod_mod]
    rw [← Nat.mul_mod]
    congr 1
    ring
  rw [hs, hp, ← mul_add, zeta_add_inv]

