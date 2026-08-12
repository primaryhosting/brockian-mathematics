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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-!
# Hückel theory for the 13-cycle

The adjacency matrix of the cycle graph `C₁₃` has spectrum `{2 cos (2πk/13) | k = 0, …, 12}`.

The proof diagonalizes the adjacency matrix by the discrete Fourier matrix
`U i j = ω^(i * j)`, where `ω = exp (2πi/13)` is a primitive 13-th root of unity.
-/

namespace Chem

open Complex Matrix

/-- A primitive 13-th root of unity. -/
noncomputable def w : ℂ := Complex.exp (2 * Real.pi * Complex.I / 13)

lemma w_primitive : IsPrimitiveRoot w 13 := by
  have := Complex.isPrimitiveRoot_exp 13 (by norm_num)
  simpa [w] using this

lemma w_pow_13 : w ^ 13 = 1 := w_primitive.pow_eq_one

lemma w_pow_mod (a : ℕ) : w ^ (a % 13) = w ^ a := by
  conv_rhs => rw [← Nat.div_add_mod a 13]
  rw [pow_add, pow_mul, w_pow_13, one_pow, one_mul]

/-- The additive character `k ↦ ω ^ k` of `Fin 13`. -/
noncomputable def zeta (k : Fin 13) : ℂ := w ^ (k.val)

lemma zeta_add (i j : Fin 13) : zeta (i + j) = zeta i * zeta j := by
  simp only [zeta, Fin.val_add, w_pow_mod, pow_add]

lemma zeta_zero : zeta 0 = 1 := by simp [zeta]

lemma zeta_pow (k c : Fin 13) : zeta (k * c) = zeta c ^ k.val := by
  simp only [zeta, Fin.val_mul, w_pow_mod, ← pow_mul, mul_comm]

lemma zeta_pow13 (c : Fin 13) : zeta c ^ 13 = 1 := by
  rw [zeta, ← pow_mul, mul_comm, pow_mul, w_pow_13, one_pow]

lemma zeta_ne_one {c : Fin 13} (hc : c ≠ 0) : zeta c ≠ 1 := by
  intro h
  have hdvd := (w_primitive.pow_eq_one_iff_dvd c.val).1 h
  have hlt : c.val < 13 := c.isLt
  have hpos : c.val ≠ 0 := fun hv => hc (Fin.val_eq_zero_iff.mp hv)
  omega

/-- Orthogonality of characters: the geometric sum of `ζ` over `Fin 13`. -/
lemma sum_zeta (c : Fin 13) :
    (∑ l : Fin 13, zeta (l * c)) = if c = 0 then 13 else 0 := by
  by_cases hc : c = 0
  · subst hc; simp [zeta]
  · simp only [hc, if_false]
    rw [Finset.sum_congr rfl (fun l _ => zeta_pow l c)]
    rw [Fin.sum_univ_eq_sum_range (fun m => (zeta c) ^ m) 13]
    rw [geom_sum_eq (zeta_ne_one hc), zeta_pow13]
    simp

lemma zeta_eq_exp (k : Fin 13) :
    zeta k = Complex.exp (((2 * Real.pi * k.val / 13 : ℝ) : ℂ) * Complex.I) := by
  rw [zeta, w, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma zeta_neg (j : Fin 13) : zeta (-j) = (zeta j)⁻¹ := by
  have h : zeta j * zeta (-j) = 1 := by rw [← zeta_add]; simp [zeta_zero]
  exact Eq.symm (DivisionMonoid.inv_eq_of_mul _ _ h)

lemma zeta_neg_add_self (j : Fin 13) :
    zeta j + zeta (-j) = 2 * (Real.cos (2 * Real.pi * j.val / 13) : ℂ) := by
  rw [zeta_neg, zeta_eq_exp, ← Complex.exp_neg]
  rw [Complex.ofReal_cos, Complex.cos]
  ring_nf

/-- The Hückel eigenvalues of `C₁₃`. -/
noncomputable def hueckelEigen (k : Fin 13) : ℂ :=
  2 * (Real.cos (2 * Real.pi * k.val / 13) : ℂ)

/-- The adjacency matrix of the cycle graph `C₁₃`. -/
noncomputable def Amat : Matrix (Fin 13) (Fin 13) ℂ :=
  (SimpleGraph.cycleGraph 13).adjMatrix ℂ

/-- The discrete Fourier matrix on `Fin 13`. -/
noncomputable def Umat : Matrix (Fin 13) (Fin 13) ℂ := fun i j => zeta (i * j)

/-- The inverse discrete Fourier matrix on `Fin 13`. -/
noncomputable def Vmat : Matrix (Fin 13) (Fin 13) ℂ := fun i j => (13 : ℂ)⁻¹ * zeta (-(i * j))

lemma sub_one_ne_add_one : ∀ i : Fin 13, i - 1 ≠ i + 1 := by decide

lemma sub_one_mul (i j : Fin 13) : (i - 1) * j = i * j + -j := by
  revert i j; decide

lemma add_one_mul' (i j : Fin 13) : (i + 1) * j = i * j + j := by
  revert i j; decide

lemma mul_sub_distrib (i j l : Fin 13) : i * l + -(l * j) = l * (i - j) := by
  revert i j l; decide

lemma Amat_apply (i l : Fin 13) : Amat i l = if l = i - 1 ∨ l = i + 1 then 1 else 0 := by
  have h : (SimpleGraph.cycleGraph 13).Adj i l ↔ (l = i - 1 ∨ l = i + 1) := by
    rw [@SimpleGraph.cycleGraph_adj 11 i l]
    constructor
    · rintro (h | h)
      · exact Or.inl (by rw [← h]; abel)
      · exact Or.inr (by rw [← h]; abel)
    · rintro (rfl | rfl)
      · exact Or.inl (by abel)
      · exact Or.inr (by abel)
  rw [Amat, SimpleGraph.adjMatrix_apply]
  simp only [h]

lemma Umat_mul_Vmat : Umat * Vmat = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  have key : ∀ l : Fin 13, Umat i l * Vmat l j = (13 : ℂ)⁻¹ * zeta (l * (i - j)) := by
    intro l
    simp only [Umat, Vmat]
    rw [← mul_sub_distrib i j l, zeta_add]
    ring
  rw [Finset.sum_congr rfl (fun l _ => key l), ← Finset.mul_sum, sum_zeta]
  by_cases h : i = j
  · subst h
    simp [Matrix.one_apply_eq]
  · rw [if_neg (sub_ne_zero.mpr h)]
    simp [Matrix.one_apply_ne h]

lemma Vmat_mul_Umat : Vmat * Umat = 1 := mul_eq_one_comm.mp Umat_mul_Vmat

lemma Amat_mul_Umat : Amat * Umat = Umat * Matrix.diagonal hueckelEigen := by
  ext i j
  rw [Matrix.mul_apply]
  have key : ∀ l : Fin 13, Amat i l * Umat l j
      = (if l = i - 1 then Umat l j else 0) + (if l = i + 1 then Umat l j else 0) := by
    intro l
    rw [Amat_apply]
    have hne : (i - 1 : Fin 13) ≠ i + 1 := sub_one_ne_add_one i
    by_cases h1 : l = i - 1
    · have h2 : l ≠ i + 1 := by rw [h1]; exact hne
      simp [h1, hne]
    · by_cases h2 : l = i + 1 <;> simp [h1, h2, Ne.symm hne]
  rw [Finset.sum_congr rfl (fun l _ => key l), Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Matrix.mul_diagonal]
  simp only [Umat, hueckelEigen]
  rw [sub_one_mul, add_one_mul', zeta_add, zeta_add, ← zeta_neg_add_self j]
  ring

/-- **Hückel theory for the 13-membered carbon ring.**  The eigenvalues (spectrum) of the
adjacency matrix of the cycle graph `C₁₃` are exactly the numbers `2 cos (2πk/13)`
for `k = 0, 1, …, 12`. -/
theorem huckel_C13 :
    spectrum ℂ ((SimpleGraph.cycleGraph 13).adjMatrix ℂ) =
      Set.range (fun k : Fin 13 => (2 * Real.cos (2 * Real.pi * k.val / 13) : ℂ)) := by
  have hA : Amat = Umat * Matrix.diagonal hueckelEigen * Vmat := by
    calc Amat = Amat * (Umat * Vmat) := by rw [Umat_mul_Vmat, mul_one]
      _ = (Amat * Umat) * Vmat := by rw [mul_assoc]
      _ = Umat * Matrix.diagonal hueckelEigen * Vmat := by rw [Amat_mul_Umat]
  have hspec : spectrum ℂ Amat = Set.range hueckelEigen := by
    let u : (Matrix (Fin 13) (Fin 13) ℂ)ˣ := ⟨Umat, Vmat, Umat_mul_Vmat, Vmat_mul_Umat⟩
    have hu : (u : Matrix (Fin 13) (Fin 13) ℂ) = Umat := rfl
    have huinv : ((u⁻¹ : (Matrix (Fin 13) (Fin 13) ℂ)ˣ) : Matrix (Fin 13) (Fin 13) ℂ) = Vmat := rfl
    rw [hA, ← hu, ← huinv, spectrum.units_conjugate, spectrum_diagonal]
  exact hspec

/-- The explicit eigenvectors: the Fourier mode `i ↦ ω^(i·k)` is an eigenvector of the
adjacency matrix of `C₁₃` with eigenvalue `2 cos (2πk/13)`. -/
theorem huckel_C13_eigenvector (k : Fin 13) :
    (SimpleGraph.cycleGraph 13).adjMatrix ℂ *ᵥ (fun i => zeta (i * k))
      = (2 * (Real.cos (2 * Real.pi * k.val / 13) : ℂ)) • (fun i => zeta (i * k)) := by
  funext i
  have h := congrFun (congrFun Amat_mul_Umat i) k
  rw [Matrix.mul_apply, Matrix.mul_diagonal] at h
  simp only [Umat] at h
  show (∑ l : Fin 13, Amat i l * zeta (l * k)) = hueckelEigen k * zeta (i * k)
  rw [h, mul_comm]

/-- The Fourier modes are nonzero, so they are genuine eigenvectors. -/
theorem huckel_C13_eigenvector_ne_zero (k : Fin 13) :
    (fun i : Fin 13 => zeta (i * k)) ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [zeta_zero] at h0

end Chem

