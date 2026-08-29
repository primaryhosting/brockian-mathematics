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

lemma kraus_rep (hB : choiMatrix Φ = Bᴴ * B) (X : Matrix (Fin N) (Fin N) ℂ) :
    Φ X = ∑ r, kraus B r * X * (kraus B r)ᴴ := by
  ext a b
  have hL : Φ X a b = ∑ i, ∑ j, X i j * Φ (Matrix.single i j 1) a b := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single X]
    simp only [map_sum, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have h : Matrix.single i j (X i j) = X i j • Matrix.single i j (1 : ℂ) := by
      simp [Matrix.smul_single]
    rw [h, map_smul]
    simp
  have hR : (∑ r, kraus B r * X * (kraus B r)ᴴ) a b
      = ∑ i, ∑ j, X i j * ∑ r, star (B r (i, a)) * B r (j, b) := by
    have e1 : (∑ r, kraus B r * X * (kraus B r)ᴴ) a b
        = ∑ r, ∑ j, ∑ i, X i j * (star (B r (i, a)) * B r (j, b)) := by
      simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, kraus,
        Matrix.of_apply, star_star, Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
        Finset.sum_congr rfl fun _ _ => by ring
    rw [e1, sum_rev3]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => (Finset.mul_sum ..).symm
  rw [hL, hR]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  have h : Φ (Matrix.single i j 1) a b = choiMatrix Φ (i, a) (j, b) := rfl
  rw [h, hB]
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- The `k`-fold amplification `I_k ⊗ V` of a Kraus operator `V`. -/
