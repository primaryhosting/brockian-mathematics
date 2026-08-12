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

namespace Chem

open Polynomial Matrix SimpleGraph

/-- The adjacency matrix of the cycle graph `C₇` (the Hückel matrix of cycloheptatrienyl,
with `α = 0`, `β = 1`), as a real `7 × 7` matrix. -/
noncomputable def C7adj : Matrix (Fin 7) (Fin 7) ℝ := (SimpleGraph.cycleGraph 7).adjMatrix ℝ

section Aux

/-- A primitive 7th root of unity. -/
noncomputable def om : ℂ := Complex.exp (2 * Real.pi * Complex.I / 7)

lemma om_prim : IsPrimitiveRoot om 7 := by
  have h := Complex.isPrimitiveRoot_exp 7 (by norm_num)
  simpa [om] using h

lemma om_pow_seven : om ^ 7 = 1 := om_prim.pow_eq_one

lemma fin7_succ_mul : ∀ k c : Fin 7, (k + 1) * c = c + k * c := by decide

lemma fin7_mul_sub_left : ∀ j k l : Fin 7, k * (j - l) = j * k + -(k * l) := by decide

lemma fin7_mul_sub_right : ∀ j k l : Fin 7, j * (l - k) = -(k * j) + j * l := by decide

lemma fin7_pred_mul : ∀ j k : Fin 7, (j - 1) * k = j * k + -k := by decide

lemma fin7_succ_mul' : ∀ j k : Fin 7, (j + 1) * k = j * k + k := by decide

/-- The additive character `Fin 7 → ℂ` given by `a ↦ ω ^ a`. -/
noncomputable def ee (a : Fin 7) : ℂ := om ^ a.val

lemma om_pow_mod (n : ℕ) : om ^ (n % 7) = om ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 7]
  rw [pow_add, pow_mul, om_pow_seven, one_pow, one_mul]

lemma ee_add (a b : Fin 7) : ee (a + b) = ee a * ee b := by
  simp only [ee, Fin.val_add, om_pow_mod, pow_add]

lemma ee_zero : ee 0 = 1 := by
  simp [ee]

lemma ee_neg (a : Fin 7) : ee (-a) = (ee a)⁻¹ := by
  have h : ee (-a) * ee a = 1 := by rw [← ee_add, neg_add_cancel, ee_zero]
  exact eq_inv_of_mul_eq_one_left h

lemma ee_ne_one {c : Fin 7} (hc : c ≠ 0) : ee c ≠ 1 := by
  have hpos : 0 < c.val := Fin.pos_iff_ne_zero.mpr hc
  exact om_prim.pow_ne_one_of_pos_of_lt hpos.ne' c.isLt

lemma sum_ee (c : Fin 7) : (∑ k : Fin 7, ee (k * c)) = if c = 0 then 7 else 0 := by
  by_cases hc : c = 0
  · subst hc
    simp [ee_zero]
  · rw [if_neg hc]
    have key : ee c * (∑ k : Fin 7, ee (k * c)) = ∑ k : Fin 7, ee (k * c) := by
      rw [Finset.mul_sum]
      have hstep : ∀ k : Fin 7, ee c * ee (k * c) = ee ((k + 1) * c) := by
        intro k
        rw [fin7_succ_mul k c, ee_add]
      simp_rw [hstep]
      exact Fintype.sum_equiv (Equiv.addRight (1 : Fin 7)) _ _ (fun _ => rfl)
    have h0 : (ee c - 1) * (∑ k : Fin 7, ee (k * c)) = 0 := by
      rw [sub_mul, one_mul, key, sub_self]
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd (sub_eq_zero.mp h) (ee_ne_one hc)
    · exact h

/-- The eigenvalues of the adjacency matrix, in complex form. -/
noncomputable def dd (k : Fin 7) : ℂ := ee k + ee (-k)

lemma dd_eq (k : Fin 7) :
    dd k = ((2 * Real.cos (2 * Real.pi * k.val / 7) : ℝ) : ℂ) := by
  have h1 : ee k = Complex.exp (((2 * Real.pi * k.val / 7 : ℝ) : ℂ) * Complex.I) := by
    rw [ee, om, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [dd, ee_neg, h1, ← Complex.exp_neg, Complex.ofReal_mul, Complex.ofReal_cos, Complex.cos]
  push_cast
  ring_nf

/-- The (unnormalized) discrete Fourier matrix. -/
noncomputable def UU : Matrix (Fin 7) (Fin 7) ℂ := Matrix.of fun j k => ee (j * k)

/-- Its inverse. -/
noncomputable def VV : Matrix (Fin 7) (Fin 7) ℂ := Matrix.of fun k l => (7 : ℂ)⁻¹ * ee (-(k * l))

lemma UU_mul_VV : UU * VV = 1 := by
  ext j l
  rw [Matrix.mul_apply]
  have hterm : ∀ k : Fin 7, UU j k * VV k l = (7 : ℂ)⁻¹ * ee (k * (j - l)) := by
    intro k
    simp only [UU, VV, Matrix.of_apply]
    rw [fin7_mul_sub_left j k l, ee_add]
    ring
  simp_rw [hterm, ← Finset.mul_sum, sum_ee]
  by_cases h : j = l
  · subst h
    simp
  · rw [if_neg (sub_ne_zero.mpr h), Matrix.one_apply_ne h, mul_zero]

lemma VV_mul_UU : VV * UU = 1 := by
  ext k l
  rw [Matrix.mul_apply]
  have hterm : ∀ j : Fin 7, VV k j * UU j l = (7 : ℂ)⁻¹ * ee (j * (l - k)) := by
    intro j
    simp only [UU, VV, Matrix.of_apply]
    rw [fin7_mul_sub_right j k l, ee_add]
    ring
  simp_rw [hterm, ← Finset.mul_sum, sum_ee]
  by_cases h : k = l
  · subst h
    simp
  · rw [if_neg (sub_ne_zero.mpr (Ne.symm h)), Matrix.one_apply_ne h, mul_zero]

lemma cycleGraph7_neighborFinset (v : Fin 7) :
    (SimpleGraph.cycleGraph 7).neighborFinset v = {v - 1, v + 1} := by
  revert v
  decide

lemma fin7_pred_ne_succ (v : Fin 7) : v - 1 ≠ v + 1 := by
  revert v
  decide

lemma adj_mul_UU : (SimpleGraph.cycleGraph 7).adjMatrix ℂ * UU = UU * Matrix.diagonal dd := by
  ext j k
  rw [SimpleGraph.adjMatrix_mul_apply, Matrix.mul_diagonal, cycleGraph7_neighborFinset,
    Finset.sum_pair (fin7_pred_ne_succ j)]
  simp only [UU, Matrix.of_apply, dd]
  rw [fin7_pred_mul j k, fin7_succ_mul' j k, ee_add, ee_add]
  ring

lemma adjC_eq : (SimpleGraph.cycleGraph 7).adjMatrix ℂ = UU * Matrix.diagonal dd * VV := by
  calc (SimpleGraph.cycleGraph 7).adjMatrix ℂ
      = (SimpleGraph.cycleGraph 7).adjMatrix ℂ * (UU * VV) := by rw [UU_mul_VV, mul_one]
    _ = ((SimpleGraph.cycleGraph 7).adjMatrix ℂ * UU) * VV := by rw [mul_assoc]
    _ = UU * Matrix.diagonal dd * VV := by rw [adj_mul_UU]

lemma charpoly_adjC :
    ((SimpleGraph.cycleGraph 7).adjMatrix ℂ).charpoly = ∏ k : Fin 7, (X - C (dd k)) := by
  let u : (Matrix (Fin 7) (Fin 7) ℂ)ˣ := ⟨UU, VV, UU_mul_VV, VV_mul_UU⟩
  have hu : ((u⁻¹ : (Matrix (Fin 7) (Fin 7) ℂ)ˣ) : Matrix (Fin 7) (Fin 7) ℂ) = VV := rfl
  have hu' : ((u : Matrix (Fin 7) (Fin 7) ℂ)) = UU := rfl
  have h := Matrix.charpoly_units_conj u (Matrix.diagonal dd)
  rw [hu, hu'] at h
  rw [adjC_eq, h, Matrix.charpoly_diagonal]

end Aux

/-- **Hückel theory for `C₇`**: the characteristic polynomial of the adjacency matrix of the
cycle graph `C₇` is `∏_{k=0}^{6} (X - 2 cos (2πk/7))`; i.e. the adjacency eigenvalues of `C₇`
are `2 cos (2πk/7)` for `k = 0, …, 6`. -/
theorem huckel_C7 :
    C7adj.charpoly =
      ∏ k : Fin 7, (X - C (2 * Real.cos (2 * Real.pi * (k : ℕ) / 7))) := by
  apply Polynomial.map_injective (Complex.ofRealHom : ℝ →+* ℂ) Complex.ofReal_injective
  rw [← Matrix.charpoly_map]
  have hmap : C7adj.map (Complex.ofRealHom : ℝ →+* ℂ) = (SimpleGraph.cycleGraph 7).adjMatrix ℂ := by
    ext i j
    by_cases h : (SimpleGraph.cycleGraph 7).Adj i j <;> simp [C7adj, h]
  rw [hmap, charpoly_adjC, Polynomial.map_prod]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  rw [dd_eq]
  simp

/-- Consequently, the set of adjacency eigenvalues of `C₇` is exactly
`{2 cos (2πk/7) : k = 0, …, 6}`. -/
theorem huckel_C7_spectrum :
    spectrum ℝ C7adj =
      Set.range (fun k : Fin 7 => 2 * Real.cos (2 * Real.pi * (k : ℕ) / 7)) := by
  ext mu
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Polynomial.IsRoot, huckel_C7]
  simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    Set.mem_range]
  rw [Finset.prod_eq_zero_iff]
  simp only [sub_eq_zero, Finset.mem_univ, true_and]
  exact exists_congr (fun _ => eq_comm)

end Chem

