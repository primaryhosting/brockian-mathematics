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

open Polynomial

/-- A primitive 8-th root of unity. -/
noncomputable def zeta8 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 8)

/-- The character `m ↦ ζ₈ ^ m` of the additive group `Fin 8`. -/
noncomputable def w8 (m : Fin 8) : ℂ := zeta8 ^ m.val

/-- The `k`-th Hückel eigenvalue of the cycle `C₈`, namely `2 cos (2πk/8)`. -/
noncomputable def huckelEigenvalue (k : Fin 8) : ℝ := 2 * Real.cos (2 * Real.pi * k.val / 8)

/-- The (unnormalised) discrete Fourier matrix of size 8. -/
noncomputable def dftMat : Matrix (Fin 8) (Fin 8) ℂ := Matrix.of fun i j => w8 (i * j)

/-- The inverse of `dftMat`. -/
noncomputable def dftInv : Matrix (Fin 8) (Fin 8) ℂ :=
  Matrix.of fun i j => (8 : ℂ)⁻¹ * w8 (-(i * j))

/-- The diagonal matrix of the Hückel eigenvalues. -/
noncomputable def eigDiag : Matrix (Fin 8) (Fin 8) ℂ :=
  Matrix.diagonal fun k : Fin 8 => ((huckelEigenvalue k : ℝ) : ℂ)

/-! ### The adjacency matrix of `C₈` -/

/-- The adjacency matrix of the cycle graph `C₈` is a circulant matrix. -/
theorem cycleGraph_adjMatrix_eq_circulant :
    ((SimpleGraph.cycleGraph 8).adjMatrix ℝ)
      = Matrix.circulant (fun i : Fin 8 => if i = 1 ∨ i = -1 then (1 : ℝ) else 0) := by
  have key : ∀ i j : Fin 8, (j = 1 + i) ↔ (i = -1 + j) := by
    intro i j
    constructor <;> (rintro rfl; abel)
  ext i j
  simp [SimpleGraph.adjMatrix, Matrix.circulant, SimpleGraph.cycleGraph_adj,
    sub_eq_iff_eq_add, key]

/-- The adjacency matrix of `C₈`, viewed over `ℂ`. -/
noncomputable def C8adjC : Matrix (Fin 8) (Fin 8) ℂ :=
  ((SimpleGraph.cycleGraph 8).adjMatrix ℝ).map (algebraMap ℝ ℂ)

theorem C8adjC_apply (i j : Fin 8) :
    C8adjC i j = if i - j = 1 ∨ i - j = -1 then 1 else 0 := by
  rw [C8adjC, Matrix.map_apply, cycleGraph_adjMatrix_eq_circulant]
  simp only [Matrix.circulant_apply]
  split <;> simp

/-! ### The eighth roots of unity -/

theorem zeta8_isPrimitiveRoot : IsPrimitiveRoot zeta8 8 := by
  have := Complex.isPrimitiveRoot_exp 8 (by norm_num)
  simpa [zeta8] using this

theorem zeta8_pow_eight : zeta8 ^ 8 = 1 := zeta8_isPrimitiveRoot.pow_eq_one

theorem zeta8_pow_mod (n : ℕ) : zeta8 ^ (n % 8) = zeta8 ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 8]
  rw [pow_add, pow_mul, zeta8_pow_eight, one_pow, one_mul]

theorem w8_zero : w8 0 = 1 := by simp [w8]

theorem w8_add (a b : Fin 8) : w8 (a + b) = w8 a * w8 b := by
  simp only [w8, Fin.val_add, ← pow_add]
  exact zeta8_pow_mod _

theorem w8_ne_zero (a : Fin 8) : w8 a ≠ 0 := by
  refine pow_ne_zero _ ?_
  simp [zeta8, Complex.exp_ne_zero]

theorem w8_neg (a : Fin 8) : w8 (-a) = (w8 a)⁻¹ := by
  have h : w8 a * w8 (-a) = 1 := by rw [← w8_add]; simp [w8_zero]
  field_simp [w8_ne_zero a] at h ⊢
  linear_combination h

theorem w8_ne_one {d : Fin 8} (hd : d ≠ 0) : w8 d ≠ 1 :=
  zeta8_isPrimitiveRoot.pow_ne_one_of_pos_of_lt
    (fun h => hd (Fin.val_eq_zero_iff.mp h)) d.isLt

/-- Orthogonality relation for the characters of `Fin 8`. -/
theorem sum_w8 (d : Fin 8) : (∑ j : Fin 8, w8 (j * d)) = if d = 0 then 8 else 0 := by
  by_cases hd : d = 0
  · subst hd
    simp [w8_zero]
  · rw [if_neg hd]
    set S : ℂ := ∑ j : Fin 8, w8 (j * d) with hS
    have hshift : w8 d * S = S := by
      have hstep : w8 d * S = ∑ j : Fin 8, w8 ((j + 1) * d) := by
        rw [hS, Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro j _
        rw [add_mul, one_mul, w8_add, mul_comm]
      rw [hstep]
      exact Fintype.sum_equiv (Equiv.addRight (1 : Fin 8)) _ _ (fun _ => rfl)
    have h1 : (w8 d - 1) * S = 0 := by linear_combination hshift
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd (by linear_combination h) (w8_ne_one hd)
    · exact h

/-- Euler's formula, in the form `ζ₈ᵏ + ζ₈⁻ᵏ = 2 cos (2πk/8)`. -/
theorem w8_add_w8_neg (k : Fin 8) :
    w8 k + w8 (-k) = ((huckelEigenvalue k : ℝ) : ℂ) := by
  have h1 : w8 k = Complex.exp ((2 * Real.pi * k.val / 8 : ℝ) * Complex.I) := by
    rw [w8, zeta8, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have h2 : w8 (-k) = Complex.exp (-((2 * Real.pi * k.val / 8 : ℝ) * Complex.I)) := by
    rw [w8_neg, h1, ← Complex.exp_neg]
  rw [h1, h2, huckelEigenvalue, Complex.ofReal_mul, Complex.ofReal_cos, Complex.cos]
  push_cast
  ring_nf

/-! ### Diagonalisation -/

/-- The columns of the discrete Fourier matrix are eigenvectors of the adjacency matrix. -/
theorem C8adjC_mul_dftMat : C8adjC * dftMat = dftMat * eigDiag := by
  have hne : ∀ i : Fin 8, i - 1 ≠ i + 1 := by decide
  have hchar : ∀ i l : Fin 8, (i - l = 1 → l = i - 1) ∧ (i - l = -1 → l = i + 1) := by decide
  have hd1 : ∀ i : Fin 8, i - (i - 1) = 1 := by decide
  have hd2 : ∀ i : Fin 8, i - (i + 1) = -1 := by decide
  have hmul1 : ∀ i j : Fin 8, (i - 1) * j = i * j + (-j) := by decide
  have hmul2 : ∀ i j : Fin 8, (i + 1) * j = i * j + j := by decide
  ext i j
  rw [Matrix.mul_apply, Matrix.mul_apply]
  have hrhs : (∑ l : Fin 8, dftMat i l * eigDiag l j)
      = w8 (i * j) * ((huckelEigenvalue j : ℝ) : ℂ) := by
    simp [eigDiag, Matrix.diagonal_apply, dftMat, eq_comm]
  rw [hrhs]
  have hlhs : ∀ l : Fin 8, C8adjC i l * dftMat l j
      = (if i - l = 1 ∨ i - l = -1 then (1 : ℂ) else 0) * w8 (l * j) := by
    intro l
    rw [C8adjC_apply, dftMat]
    rfl
  rw [Finset.sum_congr rfl (fun l _ => hlhs l),
    Finset.sum_eq_add_of_mem (i - 1) (i + 1) (Finset.mem_univ _) (Finset.mem_univ _) (hne i)
      (by
        intro c _ hc
        rw [if_neg, zero_mul]
        rintro (h | h)
        · exact hc.1 ((hchar i c).1 h)
        · exact hc.2 ((hchar i c).2 h)),
    if_pos (Or.inl (hd1 i)), if_pos (Or.inr (hd2 i)), one_mul, one_mul,
    hmul1 i j, hmul2 i j, w8_add, w8_add, ← mul_add, add_comm (w8 (-j)) (w8 j), w8_add_w8_neg]

theorem dftMat_mul_dftInv : dftMat * dftInv = 1 := by
  have hmul : ∀ i k j : Fin 8, i * j + -(j * k) = j * (i - k) := by decide
  ext i k
  rw [Matrix.mul_apply]
  have hterm : ∀ j : Fin 8, dftMat i j * dftInv j k = (8 : ℂ)⁻¹ * w8 (j * (i - k)) := by
    intro j
    rw [dftMat, dftInv]
    simp only [Matrix.of_apply]
    rw [← hmul i k j, w8_add]
    ring
  rw [Finset.sum_congr rfl (fun j _ => hterm j), ← Finset.mul_sum, sum_w8]
  by_cases h : i = k
  · subst h
    simp
  · rw [if_neg (by simpa [sub_eq_zero] using h), Matrix.one_apply_ne h, mul_zero]

/-- The discrete Fourier matrix, as a unit of the matrix ring. -/
noncomputable def dftUnit : (Matrix (Fin 8) (Fin 8) ℂ)ˣ where
  val := dftMat
  inv := dftInv
  val_inv := dftMat_mul_dftInv
  inv_val := mul_eq_one_comm.mp dftMat_mul_dftInv

theorem charpoly_C8adjC :
    C8adjC.charpoly = ∏ k : Fin 8, (X - C ((huckelEigenvalue k : ℝ) : ℂ)) := by
  have hA : C8adjC = dftUnit.val * eigDiag * (dftUnit⁻¹ : (Matrix (Fin 8) (Fin 8) ℂ)ˣ).val := by
    show C8adjC = dftMat * eigDiag * dftInv
    rw [← C8adjC_mul_dftMat, mul_assoc, dftMat_mul_dftInv, mul_one]
  rw [hA, Matrix.charpoly_units_conj, eigDiag, Matrix.charpoly_diagonal]

/-! ### The main theorem -/

/-- **Hückel theory for the cycle `C₈`.**
The characteristic polynomial of the adjacency matrix of the cycle graph `C₈` is
`∏_{k=0}^{7} (X - 2 cos (2πk/8))`; that is, the adjacency eigenvalues of `C₈`
are `2 cos (2πk/8)` for `k = 0, …, 7`. -/
theorem huckel_C8 :
    ((SimpleGraph.cycleGraph 8).adjMatrix ℝ).charpoly
      = ∏ k : Fin 8, (X - C (2 * Real.cos (2 * Real.pi * k.val / 8))) := by
  have hinj : Function.Injective (Polynomial.map (algebraMap ℝ ℂ)) :=
    Polynomial.map_injective _ (algebraMap ℝ ℂ).injective
  apply hinj
  rw [← Matrix.charpoly_map, ← C8adjC, charpoly_C8adjC, Polynomial.map_prod]
  refine Finset.prod_congr rfl ?_
  intro k _
  simp [huckelEigenvalue]

/-- The spectrum of the adjacency matrix of `C₈` is exactly the set
`{2 cos (2πk/8) : k = 0, …, 7}`. -/
theorem spectrum_C8 :
    spectrum ℝ ((SimpleGraph.cycleGraph 8).adjMatrix ℝ)
      = Set.range (fun k : Fin 8 => 2 * Real.cos (2 * Real.pi * k.val / 8)) := by
  ext x
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, huckel_C8]
  simp only [Polynomial.IsRoot.def, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, Finset.prod_eq_zero_iff, Finset.mem_univ,
    true_and, sub_eq_zero, Set.mem_range]
  exact exists_congr fun _ => eq_comm

end Chem

