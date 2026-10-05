/-
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The adjacency eigenvalues of the cycle graph `C₁₀` are `2 cos (2πk/10)`, `k = 0, …, 9`:
the characteristic polynomial of the adjacency matrix of `SimpleGraph.cycleGraph 10`
factors as `∏ k, (X - 2 cos (2πk/10))`.
-/

namespace Chem

open Polynomial Matrix

/-! ### Arithmetic in `Fin 10`

`Fin 10` carries the modular addition and multiplication of `ZMod 10`, but Mathlib does not
register a `CommRing` instance on it, so `ring` is unavailable; the few needed ring identities
are checked by `decide`. -/

set_option maxRecDepth 10000 in
lemma fin_ten_mul_sub (i j k : Fin 10) : k * (i - j) = i * k + -(k * j) := by decide +revert

set_option maxRecDepth 10000 in
lemma fin_ten_succ_mul (i k : Fin 10) : (i + 1) * k = i * k + k := by decide +revert

set_option maxRecDepth 10000 in
lemma fin_ten_pred_mul (i k : Fin 10) : (i - 1) * k = i * k + -k := by decide +revert

/-- A primitive 10-th root of unity. -/
noncomputable def zeta : ℂ := Complex.exp (2 * Real.pi * Complex.I / 10)

lemma zeta_primitive : IsPrimitiveRoot zeta 10 := by
  simpa [zeta] using Complex.isPrimitiveRoot_exp 10 (by norm_num)

lemma zeta_pow_ten : zeta ^ 10 = 1 := zeta_primitive.pow_eq_one

lemma zeta_pow_mod (m : ℕ) : zeta ^ m = zeta ^ (m % 10) := by
  conv_lhs => rw [← Nat.div_add_mod m 10]
  rw [pow_add, pow_mul, zeta_pow_ten, one_pow, one_mul]

/-- The character `k ↦ ζ^k` of `Fin 10` (indices taken modulo 10). -/
noncomputable def ee (m : Fin 10) : ℂ := zeta ^ m.val

lemma ee_add (a b : Fin 10) : ee (a + b) = ee a * ee b := by
  simp only [ee, Fin.val_add, ← zeta_pow_mod, pow_add]

lemma ee_zero : ee 0 = 1 := by simp [ee]

lemma ee_ne_zero (m : Fin 10) : ee m ≠ 0 := by
  simp [ee, Complex.exp_ne_zero, zeta]

lemma ee_neg (m : Fin 10) : ee (-m) = (ee m)⁻¹ := by
  have h : ee m * ee (-m) = 1 := by rw [← ee_add]; simp [ee_zero]
  exact (DivisionMonoid.inv_eq_of_mul _ _ h).symm

lemma ee_eq_one_iff (m : Fin 10) : ee m = 1 ↔ m = 0 := by
  constructor
  · intro h
    have := (zeta_primitive.pow_eq_one_iff_dvd m.val).mp h
    exact Fin.ext (Nat.eq_zero_of_dvd_of_lt this m.isLt)
  · rintro rfl; exact ee_zero

lemma sum_ee (m : Fin 10) : ∑ k : Fin 10, ee (k * m) = if m = 0 then 10 else 0 := by
  by_cases hm : m = 0
  · subst hm; simp [ee_zero]
  · simp only [hm, if_false]
    set S := ∑ k : Fin 10, ee (k * m) with hS
    have key : ee m * S = S := by
      have h2 : ee m * S = ∑ k : Fin 10, ee ((k + 1) * m) := by
        rw [hS, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [add_mul, one_mul, ee_add]
        ring
      rw [h2, hS]
      exact Fintype.sum_equiv (Equiv.addRight (1 : Fin 10))
        (fun k => ee ((k + 1) * m)) (fun k => ee (k * m)) (fun _ => rfl)
    have h1 : ee m - 1 ≠ 0 := sub_ne_zero.mpr fun h => hm ((ee_eq_one_iff m).mp h)
    have h3 : (ee m - 1) * S = 0 := by linear_combination key
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd h h1
    · exact h

/-- The eigenvalue attached to index `k`. -/
noncomputable def lam (k : Fin 10) : ℝ := 2 * Real.cos (2 * Real.pi * (k : ℕ) / 10)

lemma ee_eq_exp (k : Fin 10) :
    ee k = Complex.exp (((2 * Real.pi * (k : ℝ) / 10 : ℝ) : ℂ) * Complex.I) := by
  have : ((2 * Real.pi * (k : ℝ) / 10 : ℝ) : ℂ) * Complex.I
      = ((k : ℕ) : ℂ) * (2 * Real.pi * Complex.I / 10) := by push_cast; ring
  rw [this, Complex.exp_nat_mul]
  rfl

lemma lam_eq (k : Fin 10) : ((lam k : ℝ) : ℂ) = ee k + ee (-k) := by
  have h := Complex.two_cos ((2 * Real.pi * (k : ℝ) / 10 : ℝ) : ℂ)
  rw [ee_neg, ee_eq_exp, lam]
  push_cast [Complex.ofReal_cos]
  rw [← Complex.exp_neg]
  push_cast at h
  simp only [neg_mul] at h
  linear_combination h

/-- The (discrete-Fourier) eigenvector matrix. -/
noncomputable def PMat : Matrix (Fin 10) (Fin 10) ℂ := fun i k => ee (i * k)

/-- Its inverse. -/
noncomputable def QMat : Matrix (Fin 10) (Fin 10) ℂ := fun k j => (10 : ℂ)⁻¹ * ee (-(k * j))

lemma PQ : PMat * QMat = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  have hterm : ∀ k : Fin 10, PMat i k * QMat k j = (10 : ℂ)⁻¹ * ee (k * (i - j)) := by
    intro k
    simp only [PMat, QMat, fin_ten_mul_sub i j k, ee_add]
    ring
  rw [Finset.sum_congr rfl fun k _ => hterm k, ← Finset.mul_sum, sum_ee]
  by_cases h : i = j
  · subst h; norm_num
  · have : i - j ≠ 0 := sub_ne_zero.mpr h
    simp [h, this]

lemma cycleGraph_ten_adj (u v : Fin 10) :
    (SimpleGraph.cycleGraph 10).Adj u v ↔ (v = u + 1 ∨ v = u - 1) := by decide +revert

lemma adj_mul (M : Matrix (Fin 10) (Fin 10) ℂ) (i k : Fin 10) :
    (((SimpleGraph.cycleGraph 10).adjMatrix ℂ) * M) i k = M (i + 1) k + M (i - 1) k := by
  have hne : ∀ i : Fin 10, (i - 1 : Fin 10) ≠ i + 1 := by decide +revert
  rw [Matrix.mul_apply]
  have hterm : ∀ j : Fin 10, ((SimpleGraph.cycleGraph 10).adjMatrix ℂ) i j * M j k
      = (if j = i + 1 then M j k else 0) + (if j = i - 1 then M j k else 0) := by
    intro j
    rw [SimpleGraph.adjMatrix_apply]
    simp only [cycleGraph_ten_adj]
    by_cases h1 : j = i + 1
    · have h2 : j ≠ i - 1 := by rw [h1]; exact (hne i).symm
      simp [h1, (hne i).symm]
    · by_cases h2 : j = i - 1
      · simp [h2, hne i]
      · simp [h1, h2]
  rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_add_distrib]
  simp

lemma adj_mul_PMat :
    ((SimpleGraph.cycleGraph 10).adjMatrix ℂ) * PMat
      = PMat * diagonal (fun k => ((lam k : ℝ) : ℂ)) := by
  ext i k
  rw [adj_mul, Matrix.mul_diagonal, lam_eq]
  simp only [PMat, fin_ten_succ_mul i k, fin_ten_pred_mul i k, ee_add]
  ring

theorem huckel_C10 :
    ((SimpleGraph.cycleGraph 10).adjMatrix ℂ).charpoly =
      ∏ k : Fin 10, (X - C ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 10) : ℝ) : ℂ)) := by
  have hQP : QMat * PMat = 1 := mul_eq_one_comm.mp PQ
  let u : (Matrix (Fin 10) (Fin 10) ℂ)ˣ := ⟨PMat, QMat, PQ, hQP⟩
  have hA : ((SimpleGraph.cycleGraph 10).adjMatrix ℂ)
      = PMat * diagonal (fun k => ((lam k : ℝ) : ℂ)) * QMat := by
    rw [← adj_mul_PMat, Matrix.mul_assoc, PQ, Matrix.mul_one]
  rw [hA]
  exact (Matrix.charpoly_units_conj u _).trans (Matrix.charpoly_diagonal _)

/-- For each `k`, the discrete Fourier vector `i ↦ ζ^(ik)` is a nonzero eigenvector of the
adjacency matrix of `C₁₀` with eigenvalue `2 cos (2πk/10)`. -/
theorem huckel_C10_eigenvector (k : Fin 10) :
    (fun i => ee (i * k)) ≠ (0 : Fin 10 → ℂ) ∧
      ((SimpleGraph.cycleGraph 10).adjMatrix ℂ).mulVec (fun i => ee (i * k))
        = ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 10) : ℝ) : ℂ) • (fun i => ee (i * k)) := by
  constructor
  · intro h
    exact ee_ne_zero (0 * k) (congrFun h 0)
  · funext i
    have h := congrFun (congrFun adj_mul_PMat i) k
    rw [Matrix.mul_diagonal] at h
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, SimpleGraph.adjMatrix_apply, PMat, lam,
      mul_comm] using h

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

