import Mathlib

/-!
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Lean requires `import` to be the very first command of a file, so the header comment above
is placed immediately after the import.)

## Contents

The Hückel (tight-binding) Hamiltonian of the cyclic polyene `C₁₆` is `α + β A`, where `A` is the
adjacency matrix of the cycle graph `C₁₆`.  We show that the characteristic polynomial of `A`
factors as `∏_{k=0}^{15} (X - 2 cos (2 π k / 16))`, i.e. that the adjacency eigenvalues of `C₁₆`,
listed with multiplicity, are exactly `2 cos (2 π k / 16)` for `k = 0, …, 15`.

The proof diagonalises the (circulant) adjacency matrix by the discrete Fourier matrix built from
the standard additive character `ZMod.stdAddChar` of `ZMod 16`; the orthogonality relation used is
`AddChar.sum_mulShift`, and the invariance of the characteristic polynomial under conjugation comes
from `Matrix.charpoly_mul_comm`.
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Chem

open Matrix Polynomial Complex SimpleGraph

/-- The additive character `x ↦ exp (2 π I x / 16)` on `ZMod 16`. -/
noncomputable def ec : AddChar (ZMod 16) ℂ := ZMod.stdAddChar

/-- The Hückel eigenvalue `2 cos (2 π k / 16)`. -/
noncomputable def lam (k : ZMod 16) : ℂ := 2 * Real.cos (2 * Real.pi * k.val / 16)

/-- The adjacency matrix of the cycle graph `C₁₆`, with vertices indexed by `ZMod 16`
(which is the same type as `Fin 16`). -/
noncomputable def A16 : Matrix (ZMod 16) (ZMod 16) ℂ := (cycleGraph 16).adjMatrix ℂ

/-- The (unnormalised) discrete Fourier matrix of order 16. -/
noncomputable def U16 : Matrix (ZMod 16) (ZMod 16) ℂ := Matrix.of fun j k => ec (j * k)

/-- The inverse of the discrete Fourier matrix `U16`. -/
noncomputable def V16 : Matrix (ZMod 16) (ZMod 16) ℂ :=
  Matrix.of fun j k => (16 : ℂ)⁻¹ * ec (-(j * k))

lemma ec_apply (k : ZMod 16) : ec k = Complex.exp (2 * Real.pi * Complex.I * k.val / 16) := by
  rw [ec, ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  norm_num

/-- Orthogonality of the characters of `ZMod 16`. -/
lemma sum_ec (b : ZMod 16) : ∑ x : ZMod 16, ec (x * b) = if b = 0 then 16 else 0 := by
  show ∑ x : ZMod 16, ZMod.stdAddChar (x * b) = _
  rw [AddChar.sum_mulShift b (ZMod.isPrimitive_stdAddChar 16)]
  simp

lemma A16_apply (i j : ZMod 16) : A16 i j = if i - j = 1 ∨ i - j = -1 then 1 else 0 := by
  have h0 := SimpleGraph.cycleGraph_adj (n := 14) (u := i) (v := j)
  have h : (cycleGraph 16).Adj i j ↔ (i - j = 1 ∨ i - j = -1) := by
    rw [h0, ← neg_sub i j, neg_eq_iff_eq_neg]
  rw [A16, SimpleGraph.adjMatrix_apply]
  simp only [h]

lemma ec_add_ec_neg (k : ZMod 16) : ec k + ec (-k) = lam k := by
  set t : ℝ := 2 * Real.pi * k.val / 16 with ht
  have h1 : ec k = Complex.exp ((t : ℂ) * Complex.I) := by
    rw [ec_apply, ht]; push_cast; ring_nf
  have hne : ec k ≠ 0 := by rw [h1]; exact Complex.exp_ne_zero _
  have h2 : ec (-k) = (ec k)⁻¹ := by
    have h3 : ec k * ec (-k) = 1 := by
      rw [← ec.map_add_eq_mul, add_neg_cancel, ec.map_zero_eq_one]
    field_simp at h3 ⊢
    linear_combination h3
  rw [h2, h1, ← Complex.exp_neg, lam, ← ht, Complex.ofReal_cos, Complex.two_cos]
  ring_nf

lemma U16_mul_V16 : U16 * V16 = 1 := by
  ext j k
  rw [Matrix.mul_apply]
  have h : ∀ l : ZMod 16, U16 j l * V16 l k = (16 : ℂ)⁻¹ * ec (l * (j - k)) := by
    intro l
    rw [U16, V16]
    simp only [Matrix.of_apply]
    rw [show ec (j * l) * ((16 : ℂ)⁻¹ * ec (-(l * k)))
          = (16 : ℂ)⁻¹ * (ec (j * l) * ec (-(l * k))) by ring, ← ec.map_add_eq_mul]
    congr 2
    ring
  rw [Finset.sum_congr rfl (fun l _ => h l), ← Finset.mul_sum, sum_ec]
  by_cases hjk : j = k
  · subst hjk
    simp [Matrix.one_apply_eq]
  · rw [if_neg (sub_ne_zero_of_ne hjk), Matrix.one_apply_ne hjk]
    ring

/-- The Fourier matrix diagonalises the adjacency matrix of `C₁₆`. -/
lemma A16_mul_U16 : A16 * U16 = U16 * Matrix.diagonal lam := by
  ext i k
  rw [Matrix.mul_apply, Matrix.mul_diagonal]
  have hne : (i - 1 : ZMod 16) ≠ i + 1 := by
    intro h
    have h3 : (2 : ZMod 16) = 0 := by linear_combination -h
    revert h3; decide
  have key : ∀ j : ZMod 16, A16 i j * U16 j k
      = (if j = i - 1 then U16 j k else 0) + (if j = i + 1 then U16 j k else 0) := by
    intro j
    rw [A16_apply]
    have e1 : (i - j = 1) ↔ (j = i - 1) := by constructor <;> intro h <;> linear_combination -h
    have e2 : (i - j = -1) ↔ (j = i + 1) := by constructor <;> intro h <;> linear_combination -h
    simp only [e1, e2]
    by_cases h1 : j = i - 1 <;> by_cases h2 : j = i + 1 <;> simp [h1, h2, hne, hne.symm]
  rw [Finset.sum_congr rfl (fun j _ => key j), Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ (i - 1) (fun j => U16 j k),
    Finset.sum_ite_eq' Finset.univ (i + 1) (fun j => U16 j k)]
  simp only [Finset.mem_univ, if_true]
  rw [U16]
  simp only [Matrix.of_apply]
  rw [show (i - 1) * k = i * k + (-k) by ring, show (i + 1) * k = i * k + k by ring,
    ec.map_add_eq_mul, ec.map_add_eq_mul, ← mul_add, add_comm (ec (-k)) (ec k), ec_add_ec_neg]

lemma A16_charpoly : A16.charpoly = ∏ k : ZMod 16, (X - C (lam k)) := by
  have hVU : V16 * U16 = 1 := mul_eq_one_comm.mp U16_mul_V16
  have hA : A16 = U16 * Matrix.diagonal lam * V16 := by
    rw [← A16_mul_U16, Matrix.mul_assoc, U16_mul_V16, Matrix.mul_one]
  rw [hA, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hVU, Matrix.one_mul,
    Matrix.charpoly_diagonal]

/-- **Hückel theory for C₁₆.**  The characteristic polynomial of the adjacency matrix of the
cycle graph `C₁₆` is `∏_{k=0}^{15} (X - 2 cos (2 π k / 16))`; equivalently, the adjacency
eigenvalues of `C₁₆`, listed with multiplicity, are `2 cos (2 π k / 16)` for `k = 0, …, 15`. -/
theorem huckel_C16 :
    ((cycleGraph 16).adjMatrix ℂ).charpoly =
      ∏ k ∈ Finset.range 16, (X - C (2 * Real.cos (2 * Real.pi * k / 16) : ℂ)) := by
  have h : ((cycleGraph 16).adjMatrix ℂ).charpoly = A16.charpoly := rfl
  rw [h, A16_charpoly]
  rw [show (∏ k : ZMod 16, (X - C (lam k)))
      = ∏ k : Fin 16, (X - C (2 * Real.cos (2 * Real.pi * (k.val : ℝ) / 16) : ℂ)) from rfl,
    Fin.prod_univ_eq_prod_range
      (fun m => X - C (2 * Real.cos (2 * Real.pi * (m : ℝ) / 16) : ℂ)) 16]

/-- For each `k`, the discrete Fourier mode `j ↦ exp (2 π I j k / 16)` is a nonzero eigenvector
of the adjacency matrix of `C₁₆` with eigenvalue `2 cos (2 π k / 16)`. -/
theorem huckel_C16_eigenvector (k : ZMod 16) :
    (fun j : ZMod 16 => ec (j * k)) ≠ 0 ∧
      ((cycleGraph 16).adjMatrix ℂ).mulVec (fun j : ZMod 16 => ec (j * k)) =
        (2 * Real.cos (2 * Real.pi * k.val / 16) : ℂ) • fun j : ZMod 16 => ec (j * k) := by
  constructor
  · intro h
    have h0 : ec ((0 : ZMod 16) * k) = 0 := congrFun h 0
    rw [zero_mul, ec.map_zero_eq_one] at h0
    exact one_ne_zero h0
  · funext i
    have h := congrFun (congrFun A16_mul_U16 i) k
    rw [Matrix.mul_apply, Matrix.mul_diagonal] at h
    simpa [Matrix.mulVec, dotProduct, U16, lam, A16, mul_comm] using h

end Chem

