/-
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
(Note: Lean requires `import` to precede any module docstring `/-! ... -/`,
so this header is a plain block comment.)
-/

import Mathlib

namespace Chem

open Complex Matrix Polynomial

/-- A primitive 10-th root of unity. -/
noncomputable def zeta : ℂ := Complex.exp (2 * Real.pi * Complex.I / 10)

/-- The Hückel (adjacency) eigenvalues of the cycle `C₁₀`. -/
noncomputable def eig (k : Fin 10) : ℂ := 2 * Real.cos (2 * Real.pi * (k : ℕ) / 10)

/-- The discrete-Fourier (Vandermonde) matrix built from `zeta`. -/
noncomputable def Pmat : Matrix (Fin 10) (Fin 10) ℂ :=
  Matrix.vandermonde (fun i : Fin 10 => zeta ^ (i : ℕ))

/-- The adjacency matrix of the cycle graph `C₁₀`, over `ℂ`. -/
noncomputable def C10 : Matrix (Fin 10) (Fin 10) ℂ :=
  (SimpleGraph.cycleGraph 10).adjMatrix ℂ

lemma zeta_isPrimitiveRoot : IsPrimitiveRoot zeta 10 := by
  have := Complex.isPrimitiveRoot_exp 10 (by norm_num)
  simpa [zeta] using this

lemma zeta_pow_ten : zeta ^ (10 : ℕ) = 1 := zeta_isPrimitiveRoot.pow_eq_one

lemma zeta_pow_congr {a b : ℕ} (h : a % 10 = b % 10) : zeta ^ a = zeta ^ b := by
  conv_lhs => rw [← Nat.div_add_mod a 10]
  conv_rhs => rw [← Nat.div_add_mod b 10]
  rw [pow_add, pow_add, pow_mul, pow_mul, zeta_pow_ten, one_pow, one_pow, h]

lemma zeta_pow_mul_congr {a b : ℕ} (k : ℕ) (h : a % 10 = b % 10) :
    zeta ^ (a * k) = zeta ^ (b * k) :=
  zeta_pow_congr (by rw [Nat.mul_mod, h, ← Nat.mul_mod])

lemma eig_eq (k : Fin 10) : eig k = zeta ^ (k : ℕ) + zeta ^ (9 * (k : ℕ)) := by
  have h1 : zeta ^ ((k : ℕ)) = Complex.exp (((2 * Real.pi * (k : ℕ) / 10 : ℝ) : ℂ) * I) := by
    rw [zeta, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hmul : zeta ^ ((k : ℕ)) * zeta ^ (9 * (k : ℕ)) = 1 := by
    rw [← pow_add, show (k : ℕ) + 9 * (k : ℕ) = 10 * (k : ℕ) from by ring, pow_mul,
      zeta_pow_ten, one_pow]
  have h2 : zeta ^ (9 * (k : ℕ)) = Complex.exp (-((2 * Real.pi * (k : ℕ) / 10 : ℝ) : ℂ) * I) := by
    have hinv : zeta ^ (9 * (k : ℕ)) = (zeta ^ ((k : ℕ)))⁻¹ := by
      have hne : zeta ^ ((k : ℕ)) ≠ 0 := by simp [zeta, Complex.exp_ne_zero]
      field_simp
      linear_combination hmul
    rw [hinv, h1, ← Complex.exp_neg]
    congr 1
    ring
  rw [eig, h1, h2, Complex.ofReal_cos]
  exact Complex.two_cos _

lemma Pmat_apply (i k : Fin 10) : Pmat i k = zeta ^ ((i : ℕ) * (k : ℕ)) := by
  simp [Pmat, Matrix.vandermonde_apply, ← pow_mul]

/-- The key row identity: the two cyclic neighbours contribute the eigenvalue factor. -/
lemma row_id {i n₁ n₂ : ℕ} (k : ℕ) (h₁ : n₁ % 10 = (i + 1) % 10)
    (h₂ : n₂ % 10 = (i + 9) % 10) :
    zeta ^ (n₁ * k) + zeta ^ (n₂ * k) = zeta ^ (i * k) * (zeta ^ k + zeta ^ (9 * k)) := by
  rw [zeta_pow_mul_congr k h₁, zeta_pow_mul_congr k h₂, mul_add, ← pow_add, ← pow_add]
  ring_nf

lemma C10_mul_Pmat : C10 * Pmat = Pmat * Matrix.diagonal eig := by
  ext i k
  rw [Matrix.mul_apply, Matrix.mul_diagonal, Pmat_apply]
  simp only [C10, SimpleGraph.adjMatrix_apply, Pmat_apply]
  fin_cases i <;> norm_num +decide [Fin.sum_univ_succ] <;> rw [eig_eq k] <;>
  first
    | linear_combination row_id (i := 0) (n₁ := 1) (n₂ := 9) (k : ℕ) (by norm_num) (by norm_num)
    | linear_combination row_id (i := 1) (n₁ := 2) (n₂ := 0) (k : ℕ) (by norm_num) (by norm_num)
    | linear_combination row_id (i := 2) (n₁ := 3) (n₂ := 1) (k : ℕ) (by norm_num) (by norm_num)
    | linear_combination row_id (i := 3) (n₁ := 4) (n₂ := 2) (k : ℕ) (by norm_num) (by norm_num)
    | linear_combination row_id (i := 4) (n₁ := 5) (n₂ := 3) (k : ℕ) (by norm_num) (by norm_num)
    | linear_combination row_id (i := 5) (n₁ := 6) (n₂ := 4) (k : ℕ) (by norm_num) (by norm_num)
    | linear_combination row_id (i := 6) (n₁ := 7) (n₂ := 5) (k : ℕ) (by norm_num) (by norm_num)
    | linear_combination row_id (i := 7) (n₁ := 8) (n₂ := 6) (k : ℕ) (by norm_num) (by norm_num)
    | linear_combination row_id (i := 8) (n₁ := 9) (n₂ := 7) (k : ℕ) (by norm_num) (by norm_num)
    | linear_combination row_id (i := 9) (n₁ := 0) (n₂ := 8) (k : ℕ) (by norm_num) (by norm_num)

lemma Pmat_det_ne_zero : Pmat.det ≠ 0 := by
  refine Matrix.det_vandermonde_ne_zero_iff.mpr ?_
  intro i j hij
  exact Fin.ext (zeta_isPrimitiveRoot.pow_inj i.isLt j.isLt hij)

/-- **Hückel theory for the C₁₀ cycle.**  The adjacency spectrum of the cycle graph `C₁₀`
consists exactly of the numbers `2 cos (2πk/10)`, `k = 0, …, 9`, and the characteristic
polynomial factors accordingly (so these are the eigenvalues with multiplicity). -/
theorem huckel_C10 :
    spectrum ℂ ((SimpleGraph.cycleGraph 10).adjMatrix ℂ)
        = {μ : ℂ | ∃ k : Fin 10, μ = 2 * Real.cos (2 * Real.pi * (k : ℕ) / 10)} ∧
      ((SimpleGraph.cycleGraph 10).adjMatrix ℂ).charpoly
        = ∏ k : Fin 10, (X - C (2 * (Real.cos (2 * Real.pi * (k : ℕ) / 10) : ℝ) : ℂ)) := by
  have hdet : IsUnit Pmat.det := isUnit_iff_ne_zero.mpr Pmat_det_ne_zero
  set u : (Matrix (Fin 10) (Fin 10) ℂ)ˣ := ((Matrix.isUnit_iff_isUnit_det Pmat).mpr hdet).unit
  have hu' : (u : Matrix (Fin 10) (Fin 10) ℂ) = Pmat := rfl
  have hconj : C10 = (u : Matrix (Fin 10) (Fin 10) ℂ) * Matrix.diagonal eig
      * ((u⁻¹ : (Matrix (Fin 10) (Fin 10) ℂ)ˣ) : Matrix (Fin 10) (Fin 10) ℂ) := by
    rw [Matrix.coe_units_inv, hu', ← C10_mul_Pmat, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
  constructor
  · have : spectrum ℂ C10 = Set.range eig := by
      rw [hconj, spectrum.units_conjugate, spectrum_diagonal]
    rw [show ((SimpleGraph.cycleGraph 10).adjMatrix ℂ) = C10 from rfl, this]
    ext μ
    simp only [Set.mem_range, Set.mem_setOf_eq, eig]
    constructor
    · rintro ⟨k, rfl⟩; exact ⟨k, rfl⟩
    · rintro ⟨k, rfl⟩; exact ⟨k, rfl⟩
  · rw [show ((SimpleGraph.cycleGraph 10).adjMatrix ℂ) = C10 from rfl, hconj,
      Matrix.charpoly_units_conj, Matrix.charpoly_diagonal]
    rfl

end Chem

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

