/-
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Matrix Polynomial Finset

noncomputable section

/-- A primitive 18-th root of unity. -/
def zeta : ℂ := Complex.exp (2 * Real.pi * Complex.I / 18)

/-- The character `a ↦ ζ ^ a` of `ZMod 18`. -/
def wch (a : ZMod 18) : ℂ := zeta ^ a.val

/-- The adjacency matrix of the cycle graph `C₁₈`, indexed by `ZMod 18`. -/
def C18mat : Matrix (ZMod 18) (ZMod 18) ℂ :=
  Matrix.circulant (fun i => if i = 1 ∨ i = -1 then 1 else 0)

/-- The `k`-th Hückel eigenvalue `2 cos (2πk/18)`. -/
def hval (k : ZMod 18) : ℂ := ((2 * Real.cos (2 * Real.pi * k.val / 18) : ℝ) : ℂ)

/-- The (unnormalized) discrete Fourier matrix. -/
def Pmat : Matrix (ZMod 18) (ZMod 18) ℂ := fun j k => wch (j * k)

/-- Its inverse. -/
def Qmat : Matrix (ZMod 18) (ZMod 18) ℂ := fun k j => (18 : ℂ)⁻¹ * wch (-(k * j))

/-- The diagonal matrix of Hückel eigenvalues. -/
def Dmat : Matrix (ZMod 18) (ZMod 18) ℂ := diagonal hval

/-- `C18mat` really is the adjacency matrix of the 18-cycle: vertex `i` is adjacent
exactly to `i - 1` and `i + 1`. -/
theorem C18mat_apply (i j : ZMod 18) :
    C18mat i j = if j = i - 1 ∨ j = i + 1 then 1 else 0 := by
  have e1 : (i - j = 1) ↔ j = i - 1 :=
    ⟨fun h => by linear_combination -h, fun h => by linear_combination -h⟩
  have e2 : (i - j = -1) ↔ j = i + 1 :=
    ⟨fun h => by linear_combination -h, fun h => by linear_combination -h⟩
  simp only [C18mat, Matrix.circulant_apply, e1, e2]

/-- The adjacency matrix is symmetric. -/
theorem C18mat_isSymm : C18mat.IsSymm := by
  ext i j
  rw [Matrix.transpose_apply, C18mat_apply, C18mat_apply]
  have e : (i = j - 1 ∨ i = j + 1) ↔ (j = i - 1 ∨ j = i + 1) := by
    constructor <;> rintro (h | h)
    · exact Or.inr (by linear_combination -h)
    · exact Or.inl (by linear_combination -h)
    · exact Or.inr (by linear_combination -h)
    · exact Or.inl (by linear_combination -h)
  simp only [e]

theorem isPrimitiveRoot_zeta : IsPrimitiveRoot zeta 18 := by
  have := Complex.isPrimitiveRoot_exp 18 (by norm_num)
  simpa [zeta] using this

theorem zeta_pow_18 : zeta ^ 18 = 1 := isPrimitiveRoot_zeta.pow_eq_one

theorem zeta_pow_congr {a b : ℕ} (h : a % 18 = b % 18) : zeta ^ a = zeta ^ b := by
  conv_lhs => rw [← Nat.div_add_mod a 18]
  conv_rhs => rw [← Nat.div_add_mod b 18]
  rw [pow_add, pow_add, pow_mul, pow_mul, zeta_pow_18, one_pow, one_pow, h]

theorem wch_add (a b : ZMod 18) : wch (a + b) = wch a * wch b := by
  rw [wch, wch, wch, ← pow_add]
  exact zeta_pow_congr (by rw [ZMod.val_add]; simp [Nat.mod_mod_of_dvd])

theorem wch_zero : wch 0 = 1 := by simp [wch]

theorem wch_natCast_mul (n : ℕ) (c : ZMod 18) : wch ((n : ZMod 18) * c) = wch c ^ n := by
  induction n with
  | zero => simp [wch_zero]
  | succ m ih =>
      have : ((m + 1 : ℕ) : ZMod 18) * c = (m : ZMod 18) * c + c := by push_cast; ring
      rw [this, wch_add, ih, pow_succ]

theorem wch_neg_add_self (a : ZMod 18) : wch a * wch (-a) = 1 := by
  rw [← wch_add]; simp [wch_zero]

theorem wch_eq_exp (a : ZMod 18) :
    wch a = Complex.exp ((2 * Real.pi * a.val / 18 : ℝ) * Complex.I) := by
  rw [wch, zeta, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- `ζ^k + ζ^{-k} = 2 cos (2πk/18)`. -/
theorem wch_add_wch_neg (k : ZMod 18) : wch k + wch (-k) = hval k := by
  set t : ℝ := 2 * Real.pi * k.val / 18 with ht
  have h2 : wch k = Complex.exp ((t : ℂ) * Complex.I) := wch_eq_exp k
  have h3 : Complex.exp ((t : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  have hk : wch (-k) = Complex.exp (-((t : ℂ) * Complex.I)) := by
    have h1 := wch_neg_add_self k
    rw [h2] at h1
    rw [Complex.exp_neg]
    field_simp
    linear_combination h1
  rw [h2, hk, hval, ← ht, Complex.ofReal_mul, Complex.ofReal_cos, Complex.cos]
  push_cast
  ring_nf

theorem wch_ne_one {c : ZMod 18} (hc : c ≠ 0) : wch c ≠ 1 := by
  have hv : c.val ≠ 0 := fun h => hc (by
    have := ZMod.natCast_zmod_val c
    rw [h] at this; simpa using this.symm)
  exact isPrimitiveRoot_zeta.pow_ne_one_of_pos_of_lt hv (ZMod.val_lt c)

theorem sum_wch (c : ZMod 18) : ∑ k : ZMod 18, wch (k * c) = if c = 0 then 18 else 0 := by
  have hrange : ∑ k : ZMod 18, wch (k * c) = ∑ n ∈ Finset.range 18, wch ((n : ZMod 18) * c) := by
    refine Finset.sum_nbij' (fun (k : ZMod 18) => k.val) (fun (n : ℕ) => (n : ZMod 18))
      ?_ ?_ ?_ ?_ ?_
    · intro a _; simp [ZMod.val_lt]
    · intro a _; simp
    · intro a _; simp
    · intro a ha; simp only [Finset.mem_range] at ha; exact ZMod.val_natCast_of_lt ha
    · intro a _; rw [ZMod.natCast_zmod_val]
  rw [hrange]
  simp only [wch_natCast_mul]
  by_cases hc : c = 0
  · subst hc; simp [wch]
  · rw [if_neg hc]
    have h1 : wch c ≠ 1 := wch_ne_one hc
    have h18 : wch c ^ 18 = 1 := by
      rw [wch, ← pow_mul, mul_comm, pow_mul, zeta_pow_18, one_pow]
    rw [geom_sum_eq h1, h18]
    simp

theorem sum_two_terms (g : ZMod 18 → ℂ) (j : ZMod 18) :
    ∑ l : ZMod 18, (if j - l = 1 ∨ j - l = -1 then (1 : ℂ) else 0) * g l
      = g (j - 1) + g (j + 1) := by
  have hne : (j - 1 : ZMod 18) ≠ j + 1 := by
    intro h
    have : (2 : ZMod 18) = 0 := by linear_combination -h
    exact absurd this (by decide)
  have key : ∀ l : ZMod 18,
      (if j - l = 1 ∨ j - l = -1 then (1 : ℂ) else 0) * g l
        = (if l = j - 1 then g l else 0) + (if l = j + 1 then g l else 0) := by
    intro l
    have e1 : (j - l = 1) ↔ l = j - 1 := by
      constructor <;> intro h <;> linear_combination -h
    have e2 : (j - l = -1) ↔ l = j + 1 := by
      constructor <;> intro h <;> linear_combination -h
    simp only [e1, e2]
    by_cases h1 : l = j - 1 <;> by_cases h2 : l = j + 1
    · exact absurd (h1 ▸ h2) hne
    · simp [h1, hne]
    · simp [h2, Ne.symm hne]
    · simp [h1, h2]
  rw [Finset.sum_congr rfl (fun l _ => key l), Finset.sum_add_distrib]
  simp

theorem C18mat_mul_Pmat : C18mat * Pmat = Pmat * Dmat := by
  ext j k
  have lhs : (C18mat * Pmat) j k = wch ((j - 1) * k) + wch ((j + 1) * k) := by
    simp only [Matrix.mul_apply, C18mat, Matrix.circulant_apply, Pmat]
    exact sum_two_terms (fun l => wch (l * k)) j
  have rhs : (Pmat * Dmat) j k = wch (j * k) * hval k := by
    simp [Matrix.mul_apply, Dmat, Pmat, Matrix.diagonal_apply, Finset.sum_ite_eq']
  rw [lhs, rhs, ← wch_add_wch_neg k]
  have h1 : (j - 1) * k = j * k + (-k) := by ring
  have h2 : (j + 1) * k = j * k + k := by ring
  rw [h1, h2, wch_add, wch_add]
  ring

theorem Pmat_mul_Qmat : Pmat * Qmat = 1 := by
  ext j l
  rw [Matrix.mul_apply]
  have : ∀ k : ZMod 18, Pmat j k * Qmat k l = (18 : ℂ)⁻¹ * wch (k * (j - l)) := by
    intro k
    simp only [Pmat, Qmat]
    rw [← mul_assoc, mul_comm (wch (j * k)) ((18:ℂ)⁻¹), mul_assoc, ← wch_add]
    congr 2
    ring
  rw [Finset.sum_congr rfl (fun k _ => this k), ← Finset.mul_sum, sum_wch]
  by_cases h : j = l
  · subst h; simp
  · rw [if_neg (by simpa [sub_eq_zero] using h)]
    simp [h]

theorem Qmat_mul_Pmat : Qmat * Pmat = 1 := by
  ext j l
  rw [Matrix.mul_apply]
  have : ∀ k : ZMod 18, Qmat j k * Pmat k l = (18 : ℂ)⁻¹ * wch (k * (l - j)) := by
    intro k
    simp only [Pmat, Qmat]
    rw [mul_assoc, ← wch_add]
    congr 2
    ring
  rw [Finset.sum_congr rfl (fun k _ => this k), ← Finset.mul_sum, sum_wch]
  by_cases h : l = j
  · subst h; simp
  · rw [if_neg (by simpa [sub_eq_zero] using h)]
    simp [Ne.symm h]

/-- `Pmat` as a unit of the matrix ring. -/
def Punit : (Matrix (ZMod 18) (ZMod 18) ℂ)ˣ :=
  ⟨Pmat, Qmat, Pmat_mul_Qmat, Qmat_mul_Pmat⟩

theorem C18mat_eq_conj : C18mat = Pmat * Dmat * Qmat := by
  rw [← C18mat_mul_Pmat, mul_assoc, Pmat_mul_Qmat, mul_one]

/-- The eigenvector equation: the vector `j ↦ ζ^{jk}` is an eigenvector of the adjacency
matrix of `C₁₈` with eigenvalue `2 cos (2πk/18)`. -/
theorem huckel_C18_eigenvector (k : ZMod 18) :
    C18mat *ᵥ (fun j => wch (j * k)) = hval k • (fun j => wch (j * k)) := by
  funext j
  have key : (C18mat * Pmat) j k = (Pmat * Dmat) j k := by rw [C18mat_mul_Pmat]
  simp only [Matrix.mul_apply, Dmat, Pmat, Matrix.diagonal_apply] at key
  simpa [Matrix.mulVec, dotProduct, mul_comm] using key

/-- The Hückel eigenvectors are nonzero. -/
theorem huckel_C18_eigenvector_ne_zero (k : ZMod 18) :
    (fun j : ZMod 18 => wch (j * k)) ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [wch] at h0

/-- **Hückel theory for C₁₈.** The characteristic polynomial of the adjacency matrix of the
cycle graph `C₁₈` factors as `∏_{k=0}^{17} (X - 2 cos (2πk/18))`; that is, the adjacency
eigenvalues of `C₁₈` are exactly `2 cos (2πk/18)` for `k = 0, …, 17`. -/
theorem huckel_C18 :
    C18mat.charpoly =
      ∏ k ∈ Finset.range 18, (X - C ((2 * Real.cos (2 * Real.pi * k / 18) : ℝ) : ℂ)) := by
  have h1 : C18mat.charpoly = Dmat.charpoly := by
    rw [C18mat_eq_conj]
    exact Matrix.charpoly_units_conj Punit Dmat
  rw [h1, Dmat, Matrix.charpoly_diagonal]
  refine Finset.prod_nbij' (fun (k : ZMod 18) => k.val) (fun (n : ℕ) => (n : ZMod 18))
    ?_ ?_ ?_ ?_ ?_
  · intro a _; simp [ZMod.val_lt]
  · intro a _; simp
  · intro a _; simp
  · intro a ha; simp only [Finset.mem_range] at ha; exact ZMod.val_natCast_of_lt ha
  · intro a _; rw [hval]

/-- Restated as a description of the spectrum: the eigenvalues of the adjacency matrix of
`C₁₈` are exactly the numbers `2 cos (2πk/18)`, `k = 0, …, 17`. -/
theorem huckel_C18_spectrum :
    spectrum ℂ C18mat
      = {mu : ℂ | ∃ k : ℕ, k < 18 ∧ mu = ((2 * Real.cos (2 * Real.pi * k / 18) : ℝ) : ℂ)} := by
  ext x
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, huckel_C18]
  simp only [Polynomial.IsRoot.def, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, Finset.prod_eq_zero_iff, Finset.mem_range,
    sub_eq_zero, Set.mem_setOf_eq]

end

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

