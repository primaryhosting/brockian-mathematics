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

open Polynomial Matrix

/-- The primitive 17-th root of unity `exp (2πi/17)`. -/
noncomputable def zeta : ℂ := Complex.exp (2 * Real.pi * Complex.I / 17)

lemma zeta_primitiveRoot : IsPrimitiveRoot zeta 17 := by
  have := Complex.isPrimitiveRoot_exp 17 (by norm_num)
  simpa [zeta] using this

lemma zeta_pow_17 : zeta ^ (17 : ℕ) = 1 := zeta_primitiveRoot.pow_eq_one

lemma zeta_ne_zero : zeta ≠ 0 := by
  simp [zeta, Complex.exp_ne_zero]

/-- `zeta ^ a` only depends on `a` modulo `17`. -/
lemma zeta_pow_mod (a : ℕ) : zeta ^ a = zeta ^ (a % 17) := by
  conv_lhs => rw [← Nat.div_add_mod a 17]
  rw [pow_add, pow_mul, zeta_pow_17, one_pow, one_mul]

lemma zeta_pow_congr {a b : ℕ} (h : a ≡ b [MOD 17]) : zeta ^ a = zeta ^ b := by
  rw [zeta_pow_mod a, zeta_pow_mod b, h]

/-- The eigenvalues predicted by Hückel theory for the cycle `C₁₇`. -/
noncomputable def huckelEigen (k : Fin 17) : ℝ := 2 * Real.cos (2 * Real.pi * k.val / 17)

lemma zeta_pow_add_inv (m : ℕ) :
    zeta ^ m + (zeta ^ m)⁻¹ = ((2 * Real.cos (2 * Real.pi * m / 17) : ℝ) : ℂ) := by
  have h : zeta ^ m = Complex.exp ((2 * Real.pi * m / 17 : ℝ) * Complex.I) := by
    rw [zeta, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [h, ← Complex.exp_neg, Complex.exp_mul_I, ← neg_mul, Complex.exp_mul_I]
  push_cast
  simp [Complex.cos_neg, Complex.sin_neg]
  ring

lemma zeta_pow_sixteen (m : ℕ) : zeta ^ (16 * m) = (zeta ^ m)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← pow_add]
  have : 16 * m + m = 17 * m := by ring
  rw [this, pow_mul, zeta_pow_17, one_pow]

/-- The (complex) adjacency matrix of the cycle graph `C₁₇`. -/
noncomputable def A : Matrix (Fin 17) (Fin 17) ℂ := (SimpleGraph.cycleGraph 17).adjMatrix ℂ

/-- The diagonal matrix of Hückel eigenvalues. -/
noncomputable def D : Matrix (Fin 17) (Fin 17) ℂ :=
  Matrix.diagonal (fun k : Fin 17 => (huckelEigen k : ℂ))

/-- The discrete Fourier matrix. -/
noncomputable def U : Matrix (Fin 17) (Fin 17) ℂ := fun j k => zeta ^ (j.val * k.val)

/-- The inverse discrete Fourier matrix. -/
noncomputable def V : Matrix (Fin 17) (Fin 17) ℂ :=
  fun k l => (17 : ℂ)⁻¹ * (zeta ^ (k.val * l.val))⁻¹

lemma cycle_adj_iff (j l : Fin 17) :
    (SimpleGraph.cycleGraph 17).Adj j l ↔ (l = j - 1 ∨ l = j + 1) := by
  revert j l; decide

lemma sum_adj (j : Fin 17) (f : Fin 17 → ℂ) :
    ∑ l : Fin 17, A j l * f l = f (j - 1) + f (j + 1) := by
  have hfil : (Finset.univ.filter (fun l : Fin 17 => (SimpleGraph.cycleGraph 17).Adj j l))
      = {j - 1, j + 1} := by
    ext l
    simp [cycle_adj_iff]
  have hne : j - 1 ≠ j + 1 := by revert j; decide
  calc ∑ l : Fin 17, A j l * f l
      = ∑ l ∈ Finset.univ.filter (fun l : Fin 17 => (SimpleGraph.cycleGraph 17).Adj j l), f l := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl ?_
        intro l _
        by_cases h : (SimpleGraph.cycleGraph 17).Adj j l <;>
          simp [A, SimpleGraph.adjMatrix_apply, h]
    _ = f (j - 1) + f (j + 1) := by rw [hfil, Finset.sum_pair hne]

lemma fin17_sub_one_val : ∀ j : Fin 17, (j - 1).val ≡ j.val + 16 [MOD 17] := by decide

lemma fin17_add_one_val : ∀ j : Fin 17, (j + 1).val ≡ j.val + 1 [MOD 17] := by decide

lemma A_mul_U : A * U = U * D := by
  ext j k
  rw [Matrix.mul_apply, sum_adj j (fun l => U l k), D, Matrix.mul_diagonal]
  have h1 : U (j - 1) k = zeta ^ (j.val * k.val) * (zeta ^ k.val)⁻¹ := by
    show zeta ^ ((j - 1).val * k.val) = _
    rw [zeta_pow_congr (Nat.ModEq.mul_right k.val (fin17_sub_one_val j)), add_mul, pow_add,
      zeta_pow_sixteen]
  have h2 : U (j + 1) k = zeta ^ (j.val * k.val) * zeta ^ k.val := by
    show zeta ^ ((j + 1).val * k.val) = _
    rw [zeta_pow_congr (Nat.ModEq.mul_right k.val (fin17_add_one_val j)), add_mul, pow_add,
      one_mul]
  rw [h1, h2, ← mul_add, add_comm (zeta ^ k.val)⁻¹, zeta_pow_add_inv k.val]
  rfl

lemma zeta_pow_val_ne_zero (j : Fin 17) : zeta ^ j.val ≠ 0 := pow_ne_zero _ zeta_ne_zero

/-- The orthogonality relation for the 17-th roots of unity. -/
lemma geom_sum_root (j l : Fin 17) :
    ∑ k : Fin 17, (zeta ^ j.val * (zeta ^ l.val)⁻¹) ^ k.val
      = if j = l then (17 : ℂ) else 0 := by
  have hpow17 : ∀ m : ℕ, (zeta ^ m) ^ 17 = 1 := by
    intro m
    rw [← pow_mul, mul_comm, pow_mul, zeta_pow_17, one_pow]
  rw [Fin.sum_univ_eq_sum_range (fun i => (zeta ^ j.val * (zeta ^ l.val)⁻¹) ^ i) 17]
  by_cases h : j = l
  · subst h
    rw [mul_inv_cancel₀ (zeta_pow_val_ne_zero j)]
    simp
  · have hr1 : zeta ^ j.val * (zeta ^ l.val)⁻¹ ≠ 1 := by
      intro hcon
      have h2 : zeta ^ j.val = zeta ^ l.val := by
        have h3 := congrArg (fun x : ℂ => x * zeta ^ l.val) hcon
        simpa [mul_assoc, inv_mul_cancel₀ (zeta_pow_val_ne_zero l)] using h3
      exact h (Fin.ext (zeta_primitiveRoot.pow_inj j.isLt l.isLt h2))
    have h17 : (zeta ^ j.val * (zeta ^ l.val)⁻¹) ^ 17 = 1 := by
      rw [mul_pow, hpow17, inv_pow, hpow17, inv_one, mul_one]
    have hgeom := geom_sum_mul (zeta ^ j.val * (zeta ^ l.val)⁻¹) 17
    rw [h17, sub_self] at hgeom
    rcases mul_eq_zero.1 hgeom with h1 | h2
    · rw [if_neg h]
      exact h1
    · exact absurd (sub_eq_zero.1 h2) hr1

lemma U_mul_V : U * V = 1 := by
  ext j l
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hterm : ∀ k : Fin 17, U j k * V k l
      = (17 : ℂ)⁻¹ * (zeta ^ j.val * (zeta ^ l.val)⁻¹) ^ k.val := by
    intro k
    show zeta ^ (j.val * k.val) * ((17 : ℂ)⁻¹ * (zeta ^ (k.val * l.val))⁻¹) = _
    have e1 : zeta ^ (j.val * k.val) = (zeta ^ j.val) ^ k.val := by rw [pow_mul]
    have e2 : (zeta ^ (k.val * l.val))⁻¹ = ((zeta ^ l.val)⁻¹) ^ k.val := by
      rw [mul_comm, pow_mul, inv_pow]
    rw [e1, e2, mul_pow]
    ring
  rw [Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.mul_sum, geom_sum_root j l]
  by_cases h : j = l
  · rw [if_pos h, if_pos h]
    norm_num
  · rw [if_neg h, if_neg h]
    ring

lemma V_mul_U : V * U = 1 := mul_eq_one_comm.1 U_mul_V

/-- `U` as a unit of the matrix ring. -/
noncomputable def Uu : (Matrix (Fin 17) (Fin 17) ℂ)ˣ :=
  ⟨U, V, U_mul_V, V_mul_U⟩

lemma A_eq_conj :
    A = (Uu : Matrix (Fin 17) (Fin 17) ℂ) * D * ((Uu⁻¹ : (Matrix (Fin 17) (Fin 17) ℂ)ˣ) :
      Matrix (Fin 17) (Fin 17) ℂ) := by
  show A = U * D * V
  rw [← A_mul_U, mul_assoc, U_mul_V, mul_one]

lemma charpoly_A : A.charpoly = ∏ k : Fin 17, (X - C ((huckelEigen k : ℂ))) := by
  rw [A_eq_conj, Matrix.charpoly_units_conj, D, Matrix.charpoly_diagonal]

/-- The real adjacency matrix of `C₁₇`. -/
noncomputable def Areal : Matrix (Fin 17) (Fin 17) ℝ := (SimpleGraph.cycleGraph 17).adjMatrix ℝ

lemma Areal_map : Areal.map (algebraMap ℝ ℂ) = A := by
  ext j l
  by_cases h : (SimpleGraph.cycleGraph 17).Adj j l <;>
    simp [Areal, A, Matrix.map_apply, SimpleGraph.adjMatrix_apply, h]

lemma charpoly_Areal : Areal.charpoly = ∏ k : Fin 17, (X - C (huckelEigen k)) := by
  have hmap : Polynomial.map (algebraMap ℝ ℂ) Areal.charpoly
      = Polynomial.map (algebraMap ℝ ℂ) (∏ k : Fin 17, (X - C (huckelEigen k))) := by
    rw [← Matrix.charpoly_map, Areal_map, charpoly_A, Polynomial.map_prod]
    refine Finset.prod_congr rfl ?_
    intro k _
    simp
  exact Polynomial.map_injective (algebraMap ℝ ℂ) (algebraMap ℝ ℂ).injective hmap

theorem huckel_C17 :
    ((SimpleGraph.cycleGraph 17).adjMatrix ℝ).charpoly
        = ∏ k : Fin 17, (X - C (2 * Real.cos (2 * Real.pi * k.val / 17)))
      ∧ spectrum ℝ ((SimpleGraph.cycleGraph 17).adjMatrix ℝ)
        = {x : ℝ | ∃ k : Fin 17, x = 2 * Real.cos (2 * Real.pi * k.val / 17)} := by
  refine ⟨charpoly_Areal, ?_⟩
  ext x
  rw [Set.mem_setOf_eq, show ((SimpleGraph.cycleGraph 17).adjMatrix ℝ) = Areal from rfl,
    Matrix.mem_spectrum_iff_isRoot_charpoly, Polynomial.IsRoot, charpoly_Areal]
  simp [Polynomial.eval_prod, Finset.prod_eq_zero_iff, sub_eq_zero, huckelEigen]

end Chem

