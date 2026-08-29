/-
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open Complex Polynomial

namespace Chem

/-- A primitive 11-th root of unity. -/
noncomputable def zeta11 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 11)

lemma isPrimitiveRoot_zeta11 : IsPrimitiveRoot zeta11 11 := by
  simpa [zeta11] using Complex.isPrimitiveRoot_exp 11 (by norm_num)

lemma zeta11_pow_eleven : zeta11 ^ 11 = 1 := isPrimitiveRoot_zeta11.pow_eq_one

lemma zeta11_pow_congr {a b : ℕ} (h : a % 11 = b % 11) : zeta11 ^ a = zeta11 ^ b := by
  conv_lhs => rw [← Nat.div_add_mod a 11]
  conv_rhs => rw [← Nat.div_add_mod b 11]
  rw [pow_add, pow_add, pow_mul, pow_mul, zeta11_pow_eleven, one_pow, one_pow, h]

/-- The additive character `x ↦ ζ^x` on `Fin 11`. -/
noncomputable def echar (x : Fin 11) : ℂ := zeta11 ^ (x : ℕ)

lemma echar_zero : echar 0 = 1 := by simp [echar]

lemma echar_add (x y : Fin 11) : echar (x + y) = echar x * echar y := by
  rw [echar, echar, echar, ← pow_add]
  exact zeta11_pow_congr (by simp [Fin.val_add, Nat.add_mod])

lemma echar_mul (x y : Fin 11) : echar (x * y) = (echar y) ^ (x : ℕ) := by
  rw [echar, echar, ← pow_mul]
  exact zeta11_pow_congr (by simp [Fin.val_mul, Nat.mul_mod, mul_comm])

lemma echar_eq_one_iff (x : Fin 11) : echar x = 1 ↔ x = 0 := by
  constructor
  · intro h
    have hdvd := (isPrimitiveRoot_zeta11.pow_eq_one_iff_dvd (x : ℕ)).1 h
    have hx : (x : ℕ) < 11 := x.isLt
    have hx0 : (x : ℕ) = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hx
    exact Fin.ext (by simpa using hx0)
  · rintro rfl; exact echar_zero

lemma echar_neg (x : Fin 11) : echar (-x) = (echar x)⁻¹ := by
  have h : echar (-x) * echar x = 1 := by rw [← echar_add]; simp [echar_zero]
  exact eq_inv_of_mul_eq_one_left h

/-- Orthogonality of characters: the sum over all `j` of `echar (j * c)`. -/
lemma sum_echar (c : Fin 11) :
    ∑ j : Fin 11, echar (j * c) = if c = 0 then (11 : ℂ) else 0 := by
  have hpow : ∀ j : Fin 11, echar (j * c) = (echar c) ^ (j : ℕ) := fun j => echar_mul j c
  rw [Finset.sum_congr rfl (fun j _ => hpow j)]
  by_cases hc : c = 0
  · subst hc
    simp [echar_zero]
  · rw [if_neg hc]
    have hne : echar c ≠ 1 := fun h => hc ((echar_eq_one_iff c).1 h)
    have hsum : ∑ j : Fin 11, (echar c) ^ (j : ℕ) = ∑ i ∈ Finset.range 11, (echar c) ^ i :=
      (Finset.sum_range fun i => (echar c) ^ i).symm
    rw [hsum, geom_sum_eq hne]
    have h11 : (echar c) ^ 11 = 1 := by
      rw [echar, ← pow_mul, mul_comm]
      rw [pow_mul, zeta11_pow_eleven, one_pow]
    rw [h11, sub_self, zero_div]

/-- The (unnormalized) discrete Fourier matrix. -/
noncomputable def dftMat : Matrix (Fin 11) (Fin 11) ℂ := Matrix.of fun j k => echar (j * k)

/-- Its inverse. -/
noncomputable def dftMatInv : Matrix (Fin 11) (Fin 11) ℂ :=
  Matrix.of fun j k => (11 : ℂ)⁻¹ * echar (-(j * k))

lemma dft_mul_inv : dftMat * dftMatInv = 1 := by
  ext a b
  rw [Matrix.mul_apply]
  have : ∀ j : Fin 11, dftMat a j * dftMatInv j b = (11 : ℂ)⁻¹ * echar (j * (a - b)) := by
    intro j
    simp only [dftMat, dftMatInv, Matrix.of_apply]
    have hidx : j * (a - b) = a * j + -(j * b) := by revert a b j; decide
    rw [hidx, echar_add]
    ring
  rw [Finset.sum_congr rfl (fun j _ => this j), ← Finset.mul_sum, sum_echar]
  by_cases hab : a = b
  · subst hab
    simp
  · have : a - b ≠ 0 := sub_ne_zero_of_ne hab
    simp [this, hab]

lemma inv_mul_dft : dftMatInv * dftMat = 1 := by
  ext a b
  rw [Matrix.mul_apply]
  have : ∀ j : Fin 11, dftMatInv a j * dftMat j b = (11 : ℂ)⁻¹ * echar (j * (b - a)) := by
    intro j
    simp only [dftMat, dftMatInv, Matrix.of_apply]
    have hidx : j * (b - a) = -(a * j) + j * b := by revert a b j; decide
    rw [hidx, echar_add]
    ring
  rw [Finset.sum_congr rfl (fun j _ => this j), ← Finset.mul_sum, sum_echar]
  by_cases hab : a = b
  · subst hab
    simp
  · have hne : b - a ≠ 0 := sub_ne_zero_of_ne (Ne.symm hab)
    simp [hne, hab]

/-- The eigenvalue attached to index `k`. -/
noncomputable def huckelEigenvalue (k : Fin 11) : ℂ :=
  (2 * Real.cos (2 * Real.pi * (k : ℕ) / 11) : ℝ)

lemma echar_add_echar_neg (k : Fin 11) :
    echar k + echar (-k) = huckelEigenvalue k := by
  have hk : echar k = Complex.exp ((((2 * Real.pi * (k : ℕ) / 11 : ℝ)) : ℂ) * Complex.I) := by
    rw [echar, zeta11, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hnk : echar (-k) = Complex.exp (-(((2 * Real.pi * (k : ℕ) / 11 : ℝ)) : ℂ) * Complex.I) := by
    rw [echar_neg, hk, ← Complex.exp_neg]
    congr 1
    ring
  rw [hk, hnk, huckelEigenvalue]
  push_cast
  rw [Complex.cos]
  ring

lemma fin11_sub_one_ne_add_one (i : Fin 11) : i - 1 ≠ i + 1 := by revert i; decide

lemma fin11_sub_one_mul (i k : Fin 11) : (i - 1) * k = i * k + (-k) := by revert i k; decide

lemma fin11_add_one_mul (i k : Fin 11) : (i + 1) * k = i * k + k := by revert i k; decide

/-- The diagonal matrix of eigenvalues. -/
noncomputable def eigDiag : Matrix (Fin 11) (Fin 11) ℂ := Matrix.diagonal huckelEigenvalue

lemma adj_mul_dft :
    (SimpleGraph.cycleGraph 11).adjMatrix ℂ * dftMat = dftMat * eigDiag := by
  ext i k
  have hmul : ((SimpleGraph.cycleGraph 11).adjMatrix ℂ * dftMat) i k
      = ∑ u ∈ (SimpleGraph.cycleGraph 11).neighborFinset i, dftMat u k := by
    rw [Matrix.mul_apply]
    rw [← SimpleGraph.adjMatrix_mulVec_apply (α := ℂ) (G := SimpleGraph.cycleGraph 11) i
      (fun u => dftMat u k)]
    rfl
  rw [hmul, SimpleGraph.cycleGraph_neighborFinset (n := 9)]
  rw [Finset.sum_pair (fin11_sub_one_ne_add_one i)]
  simp only [dftMat, eigDiag, Matrix.of_apply, Matrix.mul_diagonal]
  rw [fin11_sub_one_mul, fin11_add_one_mul, echar_add, echar_add, ← mul_add,
    add_comm (echar (-k)) (echar k), echar_add_echar_neg]

/-- **Hückel theory for the C₁₁ ring.** The characteristic polynomial of the adjacency matrix
of the cycle graph `C₁₁` factors as `∏_{k=0}^{10} (X - 2 cos (2πk/11))`, i.e. the adjacency
eigenvalues of `C₁₁` are exactly `2 cos (2πk/11)`, `k = 0, …, 10`. -/
theorem huckel_C11 :
    ((SimpleGraph.cycleGraph 11).adjMatrix ℂ).charpoly
      = ∏ k : Fin 11, (X - C ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 11) : ℝ) : ℂ)) := by
  let U : (Matrix (Fin 11) (Fin 11) ℂ)ˣ :=
    ⟨dftMat, dftMatInv, dft_mul_inv, inv_mul_dft⟩
  have hUinv : (↑U⁻¹ : Matrix (Fin 11) (Fin 11) ℂ) = dftMatInv := rfl
  have hA : (SimpleGraph.cycleGraph 11).adjMatrix ℂ = dftMat * eigDiag * dftMatInv := by
    rw [← adj_mul_dft, mul_assoc, dft_mul_inv, mul_one]
  rw [hA]
  have := Matrix.charpoly_units_conj U eigDiag
  rw [hUinv] at this
  rw [show (↑U : Matrix (Fin 11) (Fin 11) ℂ) = dftMat from rfl] at this
  rw [this, eigDiag, Matrix.charpoly_diagonal]
  rfl

/-- The spectrum of the adjacency matrix of `C₁₁` is exactly
`{2 cos (2πk/11) : k = 0, …, 10}`. -/
theorem huckel_C11_spectrum (μ : ℂ) :
    μ ∈ spectrum ℂ ((SimpleGraph.cycleGraph 11).adjMatrix ℂ)
      ↔ ∃ k : Fin 11, μ = ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 11) : ℝ) : ℂ) := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, huckel_C11, Polynomial.IsRoot,
    Polynomial.eval_prod, Finset.prod_eq_zero_iff]
  simp [sub_eq_zero]

end Chem

