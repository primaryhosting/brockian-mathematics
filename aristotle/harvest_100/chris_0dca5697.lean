/-
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
open Complex Polynomial SimpleGraph

namespace Chem

/-- A primitive `9`-th root of unity. -/
noncomputable def zeta : ℂ := Complex.exp (2 * Real.pi * Complex.I / 9)

/-- The associated character of `ZMod 9`: `ff m = zeta ^ m`. -/
noncomputable def ff (m : ZMod 9) : ℂ := zeta ^ m.val

/-- The adjacency matrix of the cycle graph `C₉`, viewed over the index type `ZMod 9`
(which is definitionally `Fin 9`). -/
noncomputable def adjC9 : Matrix (ZMod 9) (ZMod 9) ℂ := (cycleGraph 9).adjMatrix ℂ

/-- The (Vandermonde / discrete Fourier) matrix of eigenvectors. -/
noncomputable def fourier9 : Matrix (ZMod 9) (ZMod 9) ℂ := Matrix.of fun j k => ff (j * k)

/-- The diagonal matrix of eigenvalues. -/
noncomputable def diagC9 : Matrix (ZMod 9) (ZMod 9) ℂ :=
  Matrix.diagonal fun k => ff k + ff (-k)

theorem zeta_pow_nine : zeta ^ 9 = 1 := by
  simpa [zeta] using (Complex.isPrimitiveRoot_exp 9 (by norm_num)).pow_eq_one

theorem zeta_pow_mod (n : ℕ) : zeta ^ (n % 9) = zeta ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 9, pow_add, pow_mul, zeta_pow_nine, one_pow, one_mul]

theorem ff_add (a b : ZMod 9) : ff (a + b) = ff a * ff b := by
  simp only [ff, ZMod.val_add, zeta_pow_mod, pow_add]

theorem ff_zero : ff 0 = 1 := by simp [ff]

theorem ff_neg (k : ZMod 9) : ff (-k) = (ff k)⁻¹ := by
  have h : ff k * ff (-k) = 1 := by rw [← ff_add, add_neg_cancel, ff_zero]
  exact (inv_eq_of_mul_eq_one_right h).symm

theorem ff_exp (k : ZMod 9) :
    ff k = Complex.exp (((2 * Real.pi * k.val / 9 : ℝ) : ℂ) * Complex.I) := by
  rw [ff, zeta, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The `k`-th eigenvalue is `2 cos (2πk/9)`. -/
theorem ff_add_ff_neg (k : ZMod 9) :
    ff k + ff (-k) = ((2 * Real.cos (2 * Real.pi * k.val / 9) : ℝ) : ℂ) := by
  rw [ff_neg, ff_exp, ← Complex.exp_neg, ← neg_mul, ← Complex.ofReal_neg]
  simp only [Complex.exp_mul_I, Complex.ofReal_neg, Complex.cos_neg, Complex.sin_neg]
  push_cast
  ring

/-- Entrywise description of the adjacency matrix of `C₉`. -/
theorem adjC9_apply (j l : ZMod 9) :
    adjC9 j l = (if l = j - 1 then 1 else 0) + (if l = j + 1 then 1 else 0) := by
  have h1 : (cycleGraph 9).Adj j l ↔ (j - l = 1 ∨ l - j = 1) := SimpleGraph.cycleGraph_adj
  have h2 : (j - l = 1) ↔ l = j - 1 := by
    constructor <;> (intro h; linear_combination -h)
  have h3 : (l - j = 1) ↔ l = j + 1 := by
    constructor <;> (intro h; linear_combination h)
  have hne : ∀ a : ZMod 9, a - 1 ≠ a + 1 := by decide
  simp only [adjC9, SimpleGraph.adjMatrix_apply, h1, h2, h3]
  by_cases c1 : l = j - 1 <;> by_cases c2 : l = j + 1 <;> simp_all [hne j]
  exact absurd c1.symm (hne j)

/-- The eigenvector equation `A · F = F · D`. -/
theorem adjC9_mul_fourier9 : adjC9 * fourier9 = fourier9 * diagC9 := by
  ext j k
  rw [Matrix.mul_apply, diagC9, Matrix.mul_diagonal]
  have hsum : ∑ l : ZMod 9, adjC9 j l * ff (l * k) = ff ((j - 1) * k) + ff ((j + 1) * k) := by
    simp only [adjC9_apply, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, one_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have h1 : (j - 1) * k = j * k + -k := by ring
  have h2 : (j + 1) * k = j * k + k := by ring
  simp only [fourier9, Matrix.of_apply]
  rw [hsum, h1, h2, ff_add, ff_add]
  ring

theorem fourier9_eq_vandermonde :
    fourier9 = Matrix.vandermonde (fun k : Fin 9 => zeta ^ (k : ℕ)) := by
  ext j k
  simp only [fourier9, Matrix.of_apply, Matrix.vandermonde_apply, ff, ← pow_mul]
  exact zeta_pow_mod _

theorem fourier9_det_ne_zero : fourier9.det ≠ 0 := by
  rw [fourier9_eq_vandermonde, Matrix.det_vandermonde_ne_zero_iff]
  intro a b hab
  have hp := Complex.isPrimitiveRoot_exp 9 (by norm_num)
  exact Fin.ext (hp.pow_inj a.isLt b.isLt (by simpa [zeta] using hab))

theorem charpoly_adjC9 : adjC9.charpoly = ∏ k : ZMod 9, (X - C (ff k + ff (-k))) := by
  have hu : IsUnit fourier9.det := isUnit_iff_ne_zero.mpr fourier9_det_ne_zero
  set U : (Matrix (ZMod 9) (ZMod 9) ℂ)ˣ := fourier9.nonsingInvUnit hu with hU
  have hUv : (U : Matrix (ZMod 9) (ZMod 9) ℂ) = fourier9 := rfl
  have hUi : ((U⁻¹ : (Matrix (ZMod 9) (ZMod 9) ℂ)ˣ) : Matrix (ZMod 9) (ZMod 9) ℂ) = fourier9⁻¹ :=
    rfl
  have key : adjC9 = (U : Matrix (ZMod 9) (ZMod 9) ℂ) * diagC9 *
      ((U⁻¹ : (Matrix (ZMod 9) (ZMod 9) ℂ)ˣ) : Matrix (ZMod 9) (ZMod 9) ℂ) := by
    rw [hUv, hUi, ← adjC9_mul_fourier9, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu,
      Matrix.mul_one]
  rw [key, Matrix.charpoly_units_conj, diagC9, Matrix.charpoly_diagonal]

/-- **Hückel theory for the C₉ cycle.**  The characteristic polynomial of the adjacency
matrix of the cycle graph `C₉` factors as `∏_{k=0}^{8} (X - 2 cos (2πk/9))`; equivalently,
the adjacency eigenvalues of `C₉` are `2 cos (2πk/9)` for `k = 0, …, 8`. -/
theorem huckel_C9 :
    ((cycleGraph 9).adjMatrix ℂ).charpoly =
      ∏ k ∈ Finset.range 9, (X - C ((2 * Real.cos (2 * Real.pi * k / 9) : ℝ) : ℂ)) := by
  have h := charpoly_adjC9
  rw [adjC9] at h
  rw [h, ← Fin.prod_univ_eq_prod_range
    (fun n : ℕ => (X - C ((2 * Real.cos (2 * Real.pi * n / 9) : ℝ) : ℂ))) 9]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [ff_add_ff_neg]
  rfl

/-- **The adjacency spectrum of C₉.**  The set of eigenvalues of the adjacency matrix of the
cycle graph `C₉` is exactly `{2 cos (2πk/9) : k = 0, …, 8}`. -/
theorem spectrum_adjMatrix_cycleGraph_nine :
    spectrum ℂ ((cycleGraph 9).adjMatrix ℂ) =
      {mu : ℂ | ∃ k : ℕ, k < 9 ∧ mu = ((2 * Real.cos (2 * Real.pi * k / 9) : ℝ) : ℂ)} := by
  ext mu
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, IsRoot, huckel_C9]
  simp only [eval_prod, eval_sub, eval_X, eval_C, Finset.prod_eq_zero_iff, Finset.mem_range,
    sub_eq_zero, Set.mem_setOf_eq]

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

