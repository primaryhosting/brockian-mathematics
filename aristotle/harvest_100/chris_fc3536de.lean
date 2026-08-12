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
noncomputable def zeta : ℂ := Complex.exp (2 * Real.pi * Complex.I / 16)

/-- The adjacency matrix of the cycle graph `C₁₆` (the Hückel matrix of a 16-membered
annulene, up to the usual affine normalization). -/
noncomputable def C16adj : Matrix (Fin 16) (Fin 16) ℂ :=
  (SimpleGraph.cycleGraph 16).adjMatrix ℂ

/-- The predicted Hückel eigenvalues `2 cos (2πk/16)`. -/
noncomputable def huckelEigen (k : Fin 16) : ℝ := 2 * Real.cos (2 * Real.pi * k / 16)

/-- The (discrete Fourier) matrix whose columns are the eigenvectors of `C16adj`. -/
noncomputable def dftMat : Matrix (Fin 16) (Fin 16) ℂ := fun i k => zeta ^ ((i : ℕ) * (k : ℕ))

lemma zeta_isPrimitiveRoot : IsPrimitiveRoot zeta 16 := by
  simpa [zeta] using Complex.isPrimitiveRoot_exp 16 (by norm_num)

lemma zeta_pow_sixteen : zeta ^ (16 : ℕ) = 1 := zeta_isPrimitiveRoot.pow_eq_one

lemma zeta_pow_congr {a b : ℕ} (h : a % 16 = b % 16) : zeta ^ a = zeta ^ b := by
  conv_lhs => rw [← Nat.div_add_mod a 16]
  conv_rhs => rw [← Nat.div_add_mod b 16]
  simp [pow_add, pow_mul, zeta_pow_sixteen, h]

lemma zeta_pow_eq_exp (k : ℕ) :
    zeta ^ k = Complex.exp (((2 * Real.pi * k / 16 : ℝ) : ℂ) * Complex.I) := by
  rw [zeta, ← Complex.exp_nat_mul]
  push_cast
  ring_nf

lemma zeta_pow_fifteen_mul (k : ℕ) : zeta ^ (15 * k) = (zeta ^ k)⁻¹ := by
  refine eq_inv_of_mul_eq_one_right ?_
  rw [← pow_add, show k + 15 * k = 16 * k by ring, pow_mul, zeta_pow_sixteen, one_pow]

/-- The key trigonometric identity: `ζ^k + ζ^(-k) = 2 cos (2πk/16)`. -/
lemma zeta_add_inv (k : ℕ) :
    zeta ^ k + zeta ^ (15 * k) = ((2 * Real.cos (2 * Real.pi * k / 16) : ℝ) : ℂ) := by
  rw [zeta_pow_fifteen_mul, zeta_pow_eq_exp, ← Complex.exp_neg]
  push_cast
  rw [Complex.two_cos]
  ring_nf

lemma adj_iff (i j : Fin 16) :
    (SimpleGraph.cycleGraph 16).Adj i j ↔ (j = i + 1 ∨ j = i - 1) := by
  revert i j
  decide

lemma succ_val (i : Fin 16) : ((i + 1 : Fin 16) : ℕ) = (i.val + 1) % 16 := by
  revert i; decide

lemma pred_val (i : Fin 16) : ((i - 1 : Fin 16) : ℕ) = (i.val + 15) % 16 := by
  revert i; decide

lemma succ_ne_pred (i : Fin 16) : (i + 1 : Fin 16) ≠ i - 1 := by
  revert i; decide

/-- Multiplying by the adjacency matrix sums the two neighbouring entries. -/
lemma adjMatrix_mul_apply (M : Matrix (Fin 16) (Fin 16) ℂ) (i k : Fin 16) :
    (C16adj * M) i k = M (i + 1) k + M (i - 1) k := by
  classical
  simp only [C16adj, Matrix.mul_apply, SimpleGraph.adjMatrix_apply]
  have h1 : ∀ j : Fin 16,
      (if (SimpleGraph.cycleGraph 16).Adj i j then (1 : ℂ) else 0) * M j k
        = if (j = i + 1 ∨ j = i - 1) then M j k else 0 := by
    intro j
    by_cases h : (SimpleGraph.cycleGraph 16).Adj i j
    · rw [if_pos h, if_pos ((adj_iff i j).1 h), one_mul]
    · rw [if_neg h, if_neg (fun hh => h ((adj_iff i j).2 hh)), zero_mul]
  have h2 : (Finset.univ : Finset (Fin 16)).filter (fun j => j = i + 1 ∨ j = i - 1)
      = {i + 1, i - 1} := by
    ext j
    simp
  rw [Finset.sum_congr rfl (fun j _ => h1 j), ← Finset.sum_filter, h2,
    Finset.sum_pair (succ_ne_pred i)]

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

lemma dft_det_ne_zero : (dftMat).det ≠ 0 := by
  have hvan : dftMat = Matrix.vandermonde (fun i : Fin 16 => zeta ^ (i : ℕ)) := by
    ext i k
    simp [dftMat, Matrix.vandermonde, ← pow_mul]
  rw [hvan, Matrix.det_vandermonde_ne_zero_iff]
  intro i j hij
  exact Fin.ext (zeta_isPrimitiveRoot.pow_inj i.isLt j.isLt hij)

/-- The adjacency matrix of `C₁₆` is conjugate (by the discrete Fourier matrix) to the
diagonal matrix of the values `2 cos (2πk/16)`. -/
lemma exists_unit_conj_diagonal :
    ∃ u : (Matrix (Fin 16) (Fin 16) ℂ)ˣ,
      ((SimpleGraph.cycleGraph 16).adjMatrix ℂ)
        = (u : Matrix (Fin 16) (Fin 16) ℂ)
            * Matrix.diagonal (fun k => ((huckelEigen k : ℝ) : ℂ))
            * (↑u⁻¹ : Matrix (Fin 16) (Fin 16) ℂ) := by
  have hdet : IsUnit (dftMat).det := Ne.isUnit dft_det_ne_zero
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det dftMat).2 hdet
  refine ⟨u, ?_⟩
  have h := adj_mul_dft
  rw [← hu] at h
  calc ((SimpleGraph.cycleGraph 16).adjMatrix ℂ)
      = (C16adj * (u : Matrix (Fin 16) (Fin 16) ℂ))
          * (↑u⁻¹ : Matrix (Fin 16) (Fin 16) ℂ) := by
        rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]; rfl
    _ = (u : Matrix (Fin 16) (Fin 16) ℂ)
          * Matrix.diagonal (fun k => ((huckelEigen k : ℝ) : ℂ))
          * (↑u⁻¹ : Matrix (Fin 16) (Fin 16) ℂ) := by
        rw [h]

/-- **Hückel theory for the 16-annulene.**  The spectrum of the adjacency matrix of the
cycle graph `C₁₆` is exactly `{2 cos (2πk/16) : k = 0, …, 15}`. -/
theorem huckel_C16 :
    spectrum ℂ ((SimpleGraph.cycleGraph 16).adjMatrix ℂ)
      = {μ : ℂ | ∃ k : Fin 16, μ = 2 * Real.cos (2 * Real.pi * k / 16)} := by
  obtain ⟨u, hconj⟩ := exists_unit_conj_diagonal
  rw [hconj, spectrum.units_conjugate, spectrum_diagonal]
  ext μ
  simp only [Set.mem_range, Set.mem_setOf_eq, huckelEigen]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, by push_cast; ring⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, by push_cast; ring⟩

/-- The characteristic polynomial of the adjacency matrix of `C₁₆` factors as
`∏_{k=0}^{15} (X - 2 cos (2πk/16))`; i.e. the sixteen eigenvalues, counted with
multiplicity, are the numbers `2 cos (2πk/16)`, `k = 0, …, 15`. -/
theorem huckel_C16_charpoly :
    ((SimpleGraph.cycleGraph 16).adjMatrix ℂ).charpoly
      = ∏ k : Fin 16, (Polynomial.X
          - Polynomial.C ((2 * Real.cos (2 * Real.pi * k / 16) : ℝ) : ℂ)) := by
  obtain ⟨u, hconj⟩ := exists_unit_conj_diagonal
  rw [hconj, Matrix.charpoly_units_conj, Matrix.charpoly_diagonal]
  rfl

end Chem

