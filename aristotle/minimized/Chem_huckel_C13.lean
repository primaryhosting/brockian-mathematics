import Mathlib

/-!
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
open scoped Real

namespace Chem

/-! ### A primitive 13-th root of unity -/

/-- A primitive 13-th root of unity. -/

noncomputable def zeta13 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 13)

lemma zeta13_primitive : IsPrimitiveRoot zeta13 13 :=
  Complex.isPrimitiveRoot_exp 13 (by norm_num)

lemma zeta13_pow_13 : zeta13 ^ 13 = 1 := zeta13_primitive.pow_eq_one

/-- If `w ^ 13 = 1` then `w ^ (·)` factors through `Fin 13` and turns addition into
multiplication. -/

lemma pow_val_add {w : ℂ} (hw : w ^ 13 = 1) (a b : Fin 13) :
    w ^ ((a + b) : Fin 13).val = w ^ a.val * w ^ b.val := by
  have hmod : ∀ m : ℕ, w ^ (m % 13) = w ^ m := by
    intro m
    conv_rhs => rw [← Nat.div_add_mod m 13]
    rw [pow_add, pow_mul, hw, one_pow, one_mul]
  rw [Fin.val_add, hmod, pow_add]

/-- The character `Fin 13 → ℂ`, `a ↦ ζ ^ a`. -/

noncomputable def qc (a : Fin 13) : ℂ := zeta13 ^ (a : ℕ)

lemma qc_pow_13 (k : Fin 13) : (qc k) ^ 13 = 1 := by
  rw [qc, ← pow_mul, mul_comm, pow_mul, zeta13_pow_13, one_pow]

lemma qc_ne_zero (a : Fin 13) : qc a ≠ 0 :=
  pow_ne_zero _ (Complex.exp_ne_zero _)

lemma qc_injective : Function.Injective qc := fun a b hab =>
  Fin.ext (zeta13_primitive.pow_inj a.isLt b.isLt hab)

lemma qc_eq_exp (k : Fin 13) :
    qc k = Complex.exp (((2 * Real.pi * (k : ℕ) / 13 : ℝ) : ℂ) * Complex.I) := by
  rw [qc, zeta13, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The eigenvalue attached to the character `k`: `ζ^k + ζ^{-k} = 2 cos (2πk/13)`. -/

lemma qc_add_qc_inv (k : Fin 13) :
    qc k + (qc k)⁻¹ = ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 13) : ℝ) : ℂ) := by
  have h1 : (qc k)⁻¹ = Complex.exp (-(((2 * Real.pi * (k : ℕ) / 13 : ℝ) : ℂ) * Complex.I)) := by
    rw [qc_eq_exp, ← Complex.exp_neg]
  rw [h1, qc_eq_exp]
  push_cast
  rw [Complex.cos, neg_mul]
  ring

/-! ### Diagonalisation of the adjacency matrix of `C₁₃` -/

/-- The adjacency matrix of the 13-cycle, over `ℂ`. -/

noncomputable def A13 : Matrix (Fin 13) (Fin 13) ℂ := (SimpleGraph.cycleGraph 13).adjMatrix ℂ

/-- The discrete Fourier (Vandermonde) matrix diagonalising `A13`. -/

noncomputable def P13 : Matrix (Fin 13) (Fin 13) ℂ := Matrix.vandermonde fun j => qc j

/-- The diagonal matrix of Hückel eigenvalues. -/

noncomputable def D13 : Matrix (Fin 13) (Fin 13) ℂ :=
  Matrix.diagonal fun k : Fin 13 => ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 13) : ℝ) : ℂ)

/-- The `(j, k)` entry of `P13` is the `j`-th power of the `k`-th root of unity. -/

lemma P13_apply (j k : Fin 13) : P13 j k = (qc k) ^ (j : ℕ) := by
  simp only [P13, Matrix.vandermonde_apply, qc, ← pow_mul]
  rw [Nat.mul_comm]

lemma P13_isUnit : IsUnit P13 := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, P13, Matrix.det_vandermonde]
  refine Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j hj => ?_
  simp only [Finset.mem_Ioi] at hj
  exact sub_ne_zero_of_ne fun h => absurd (qc_injective h) hj.ne'

lemma P13_isUnit_det : IsUnit P13.det := (Matrix.isUnit_iff_isUnit_det _).1 P13_isUnit

lemma neighborFinset_cycle13 (j : Fin 13) :
    (SimpleGraph.cycleGraph 13).neighborFinset j = {j - 1, j + 1} :=
  SimpleGraph.cycleGraph_neighborFinset (n := 11) (v := j)

/-- The key computation: `A · P = P · D`, i.e. the columns of `P` are eigenvectors of `A`. -/

lemma A13_mul_P13 : A13 * P13 = P13 * D13 := by
  have hne : ∀ i : Fin 13, i - 1 ≠ i + 1 := by decide
  ext j k
  have hcol : (A13 * P13) j k = ∑ l ∈ (SimpleGraph.cycleGraph 13).neighborFinset j, P13 l k := by
    have h := SimpleGraph.adjMatrix_mulVec_apply (α := ℂ) (SimpleGraph.cycleGraph 13) j
      (fun l => P13 l k)
    simpa [A13, Matrix.mul_apply, Matrix.mulVec, dotProduct, SimpleGraph.adjMatrix_apply,
      ite_mul] using h
  have hw : (qc k) ^ 13 = 1 := qc_pow_13 k
  have hw0 : qc k ≠ 0 := qc_ne_zero k
  have h1 : (qc k) ^ ((1 : Fin 13)).val = qc k := by norm_num
  have hminus : (qc k) ^ ((j - 1 : Fin 13)).val = (qc k) ^ (j : ℕ) * (qc k)⁻¹ := by
    have h2 := pow_val_add hw (j - 1) 1
    rw [sub_add_cancel, h1] at h2
    field_simp
    linear_combination -h2
  have hplus : (qc k) ^ ((j + 1 : Fin 13)).val = (qc k) ^ (j : ℕ) * qc k := by
    have h2 := pow_val_add hw j 1
    rwa [h1] at h2
  rw [hcol, neighborFinset_cycle13, Finset.sum_pair (hne j), P13_apply, P13_apply, D13,
    Matrix.mul_diagonal, P13_apply, hminus, hplus, ← qc_add_qc_inv k]
  ring

lemma A13_eq_conj : A13 = P13 * D13 * P13⁻¹ := by
  have hinv : P13 * P13⁻¹ = 1 := Matrix.mul_nonsing_inv _ P13_isUnit_det
  calc A13 = A13 * (P13 * P13⁻¹) := by rw [hinv, mul_one]
    _ = A13 * P13 * P13⁻¹ := by rw [Matrix.mul_assoc]
    _ = P13 * D13 * P13⁻¹ := by rw [A13_mul_P13]

/-- **Hückel theory for C₁₃**: the adjacency eigenvalues of the cycle graph `C₁₃` are exactly
the numbers `2 cos (2πk/13)` for `k = 0, …, 12`. -/

theorem huckel_C13 :
    spectrum ℂ ((SimpleGraph.cycleGraph 13).adjMatrix ℂ) =
      {z : ℂ | ∃ k : Fin 13, z = ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 13) : ℝ) : ℂ)} := by
  obtain ⟨u, hu⟩ := P13_isUnit
  have hA : ((SimpleGraph.cycleGraph 13).adjMatrix ℂ)
      = (u : Matrix (Fin 13) (Fin 13) ℂ) * D13 * ((u⁻¹ : (Matrix (Fin 13) (Fin 13) ℂ)ˣ) :
        Matrix (Fin 13) (Fin 13) ℂ) := by
    rw [Matrix.coe_units_inv, hu]
    exact A13_eq_conj
  rw [hA, spectrum.units_conjugate, D13, spectrum_diagonal]
  ext z
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, rfl⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, rfl⟩

/-- Explicit eigenvectors: the vector `j ↦ exp (2πi jk/13)` is a nonzero eigenvector of the
adjacency matrix of `C₁₃` with eigenvalue `2 cos (2πk/13)`. -/
