/-
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is a plain comment because Lean requires `import` lines to
-- precede any module docstring; the same text is repeated verbatim below.)
import Mathlib

/-!
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QI

open Matrix Finset
open scoped ComplexOrder MatrixOrder

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The Choi matrix of a linear map `Φ : Mₙ(ℂ) →ₗ Mₘ(ℂ)`:
`C (i,k) (j,l) = (Φ Eᵢⱼ) k l`, where the `Eᵢⱼ` are the matrix units. -/

theorem hasKrausDecomposition_of_choiMatrix_posSemidef (h : (choiMatrix Φ).PosSemidef) :
    HasKrausDecomposition Φ := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp
    (Matrix.nonneg_iff_posSemidef.mpr h)
  classical
  set N := Fintype.card (n × m)
  set e : Fin N ≃ (n × m) := (Fintype.equivFin (n × m)).symm
  refine ⟨N, fun a => Matrix.of fun k i => (starRingEnd ℂ) (B (e a) (i, k)), ?_⟩
  intro X
  ext k l
  have hX : Φ X = ∑ i : n, ∑ j : n, X i j • Φ (Matrix.single i j 1) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single X]
    simp only [map_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [show Matrix.single i j (X i j) = X i j • Matrix.single i j (1 : ℂ) by
      rw [Matrix.smul_single]; simp]
    rw [map_smul]
  have hentry : ∀ i j : n, Φ (Matrix.single i j 1) k l
      = ∑ a : Fin N, (starRingEnd ℂ) (B (e a) (i, k)) * B (e a) (j, l) := by
    intro i j
    have : Φ (Matrix.single i j 1) k l = choiMatrix Φ (i, k) (j, l) := rfl
    rw [this, hB]
    simp only [Matrix.mul_apply]
    exact (Equiv.sum_comp e fun c => (starRingEnd ℂ) (B c (i, k)) * B c (j, l)).symm
  rw [hX]
  have hswap : ∀ f : n → n → Fin N → ℂ,
      (∑ i : n, ∑ j : n, ∑ a : Fin N, f i j a) = ∑ a : Fin N, ∑ i : n, ∑ j : n, f i j a := by
    intro f
    rw [show (∑ i : n, ∑ j : n, ∑ a : Fin N, f i j a)
        = ∑ i : n, ∑ a : Fin N, ∑ j : n, f i j a from
      Finset.sum_congr rfl fun i _ => Finset.sum_comm]
    exact Finset.sum_comm
  calc (∑ i : n, ∑ j : n, X i j • Φ (Matrix.single i j 1)) k l
      = ∑ i : n, ∑ j : n, ∑ a : Fin N,
          X i j * ((starRingEnd ℂ) (B (e a) (i, k)) * B (e a) (j, l)) := by
        simp [Matrix.sum_apply, hentry, Finset.mul_sum]
    _ = ∑ a : Fin N, ∑ i : n, ∑ j : n,
          X i j * ((starRingEnd ℂ) (B (e a) (i, k)) * B (e a) (j, l)) := hswap _
    _ = (∑ a : Fin N, (Matrix.of fun k i => (starRingEnd ℂ) (B (e a) (i, k))) * X *
          ((Matrix.of fun k i => (starRingEnd ℂ) (B (e a) (i, k))) : Matrix m n ℂ)ᴴ) k l := by
        rw [Matrix.sum_apply]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [matrix_conj_apply]
        simp

omit [Fintype m] [DecidableEq m] in
/-- If `Φ` is completely positive then its Choi matrix is positive semidefinite. -/
