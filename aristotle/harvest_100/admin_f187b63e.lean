/-
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix Complex Finset

namespace Chem

/-- The circulant form of the adjacency matrix of the cycle graph `C₁₁`,
with vertices indexed by `ZMod 11`. -/
noncomputable def cycAdj : Matrix (ZMod 11) (ZMod 11) ℂ :=
  Matrix.circulant (fun d => if d = 1 ∨ d = -1 then 1 else 0)

/-- The adjacency matrix of `SimpleGraph.cycleGraph 11` is the circulant matrix `cycAdj`. -/
theorem adjMatrix_cycleGraph_eq : (SimpleGraph.cycleGraph 11).adjMatrix ℂ = cycAdj := by
  ext i j
  have h : (i - j = -1) ↔ (j - i = 1) := by
    rw [← neg_inj, neg_sub]; simp
  simp [SimpleGraph.adjMatrix_apply, cycAdj, Matrix.circulant, SimpleGraph.cycleGraph_adj, h]

/-- The standard additive character of `ZMod 11`, `k ↦ exp (2πik/11)`. -/
noncomputable abbrev ee : AddChar (ZMod 11) ℂ := ZMod.stdAddChar

/-- The discrete Fourier matrix `P i k = exp (2πi·ik/11)`. -/
noncomputable def fourierP : Matrix (ZMod 11) (ZMod 11) ℂ := fun i k => ee (i * k)

/-- The inverse of the discrete Fourier matrix. -/
noncomputable def fourierQ : Matrix (ZMod 11) (ZMod 11) ℂ :=
  fun k j => (11 : ℂ)⁻¹ * ee (-(k * j))

/-- The eigenvalues, as a function on `ZMod 11`. -/
noncomputable def eigVal (k : ZMod 11) : ℂ := ee k + ee (-k)

/-- Orthogonality relation for the standard additive character of `ZMod 11`. -/
theorem sum_char (t : ZMod 11) : ∑ i : ZMod 11, ee (t * i) = if t = 0 then (11 : ℂ) else 0 := by
  split_ifs with h
  · simp [h]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar 11 h)

theorem fourierP_mul_fourierQ : fourierP * fourierQ = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  have key : ∀ k : ZMod 11, fourierP i k * fourierQ k j = (11 : ℂ)⁻¹ * ee ((i - j) * k) := by
    intro k
    simp only [fourierP, fourierQ]
    rw [show (i - j) * k = i * k + (-(k * j)) by ring, AddChar.map_add_eq_mul]
    ring
  rw [Finset.sum_congr rfl (fun k _ => key k), ← Finset.mul_sum, sum_char]
  by_cases h : i = j
  · subst h; norm_num
  · have h2 : i - j ≠ 0 := sub_ne_zero_of_ne h
    simp [h2, h]

theorem fourierQ_mul_fourierP : fourierQ * fourierP = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  have key : ∀ k : ZMod 11, fourierQ i k * fourierP k j = (11 : ℂ)⁻¹ * ee ((j - i) * k) := by
    intro k
    simp only [fourierP, fourierQ]
    rw [show (j - i) * k = (-(i * k)) + k * j by ring, AddChar.map_add_eq_mul]
    ring
  rw [Finset.sum_congr rfl (fun k _ => key k), ← Finset.mul_sum, sum_char]
  by_cases h : i = j
  · subst h; norm_num
  · have h2 : j - i ≠ 0 := sub_ne_zero_of_ne (Ne.symm h)
    simp [h2, h]

/-- The Fourier matrix, as a unit of the matrix ring. -/
noncomputable def fourierU : (Matrix (ZMod 11) (ZMod 11) ℂ)ˣ :=
  ⟨fourierP, fourierQ, fourierP_mul_fourierQ, fourierQ_mul_fourierP⟩

/-- The columns of the Fourier matrix diagonalise the adjacency matrix. -/
theorem cycAdj_mul_fourierP : cycAdj * fourierP = fourierP * Matrix.diagonal eigVal := by
  ext i k
  rw [Matrix.mul_apply, Matrix.mul_diagonal]
  have hne : (i - 1 : ZMod 11) ≠ i + 1 := by
    intro h
    have h2 : (2 : ZMod 11) = 0 := by linear_combination -h
    exact absurd h2 (by decide)
  have key : ∀ j : ZMod 11, cycAdj i j * fourierP j k
      = (if j = i - 1 then fourierP j k else 0) + (if j = i + 1 then fourierP j k else 0) := by
    intro j
    have h1 : (i - j = 1) ↔ (j = i - 1) := by
      constructor <;> intro h <;> linear_combination -h
    have h2 : (i - j = -1) ↔ (j = i + 1) := by
      constructor <;> intro h <;> linear_combination -h
    simp only [cycAdj, Matrix.circulant_apply, h1, h2]
    by_cases ha : j = i - 1 <;> by_cases hb : j = i + 1 <;> simp [ha, hb] <;>
      first
        | (intro hc; exact absurd hc hne)
        | (intro hc; exact absurd hc.symm hne)
  rw [Finset.sum_congr rfl (fun j _ => key j), Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ (i - 1) (fun j => fourierP j k),
    Finset.sum_ite_eq' Finset.univ (i + 1) (fun j => fourierP j k)]
  simp only [Finset.mem_univ, if_true, fourierP, eigVal]
  rw [show (i - 1) * k = i * k + (-k) by ring, show (i + 1) * k = i * k + k by ring,
    AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
  ring

/-- The `k`-th eigenvalue is `2 cos (2πk/11)`. -/
theorem eigVal_eq (k : ZMod 11) :
    eigVal k = ((2 * Real.cos (2 * Real.pi * k.val / 11) : ℝ) : ℂ) := by
  have hk : ((k.val : ℤ) : ZMod 11) = k := by push_cast; simp
  have h1 : ee k = Complex.exp ((2 * Real.pi * k.val / 11 : ℝ) * I) := by
    conv_lhs => rw [← hk]
    rw [ZMod.stdAddChar_coe]
    push_cast
    ring_nf
  rw [eigVal, AddChar.map_neg_eq_inv, h1, ← Complex.exp_neg]
  push_cast
  rw [Complex.two_cos]
  ring_nf

theorem spectrum_diagonal_eq (d : ZMod 11 → ℂ) :
    spectrum ℂ (Matrix.diagonal d) = Set.range d := by
  ext z
  rw [spectrum.mem_iff]
  have halg : (algebraMap ℂ (Matrix (ZMod 11) (ZMod 11) ℂ)) z - Matrix.diagonal d
      = Matrix.diagonal (fun i => z - d i) := by
    rw [Matrix.algebraMap_eq_diagonal, ← Matrix.diagonal_sub]
    rfl
  rw [halg, Matrix.isUnit_iff_isUnit_det, Matrix.det_diagonal, isUnit_iff_ne_zero,
    not_not, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨i, -, hi⟩
    exact ⟨i, (sub_eq_zero.mp hi).symm⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, Finset.mem_univ i, by rw [← hi]; ring⟩

/-- **Hückel theory for the C₁₁ cycle.**  The eigenvalues (spectrum) of the adjacency matrix
of the cycle graph `C₁₁` are exactly the numbers `2 cos (2πk/11)` for `k = 0, …, 10`. -/
theorem huckel_C11 :
    spectrum ℂ ((SimpleGraph.cycleGraph 11).adjMatrix ℂ) =
      {z : ℂ | ∃ k : ℕ, k ≤ 10 ∧ z = ((2 * Real.cos (2 * Real.pi * k / 11) : ℝ) : ℂ)} := by
  have hconj : cycAdj = (fourierU : Matrix (ZMod 11) (ZMod 11) ℂ) * Matrix.diagonal eigVal
      * (↑fourierU⁻¹ : Matrix (ZMod 11) (ZMod 11) ℂ) := by
    show cycAdj = fourierP * Matrix.diagonal eigVal * fourierQ
    rw [← cycAdj_mul_fourierP, mul_assoc, fourierP_mul_fourierQ, mul_one]
  rw [adjMatrix_cycleGraph_eq, hconj, spectrum.units_conjugate, spectrum_diagonal_eq]
  ext z
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k.val, by have := ZMod.val_lt k; omega, eigVal_eq k⟩
  · rintro ⟨n, hn, rfl⟩
    refine ⟨(n : ZMod 11), ?_⟩
    rw [eigVal_eq, ZMod.val_natCast_of_lt (by omega)]

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

