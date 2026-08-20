/-
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Polynomial SimpleGraph

/-- The adjacency matrix (Hückel matrix, with `α = 0`, `β = 1`) of the cycle graph `C₁₄`. -/
noncomputable def C14adj : Matrix (Fin 14) (Fin 14) ℂ :=
  (cycleGraph 14).adjMatrix ℂ

/-- The primitive 14-th root of unity `exp (2πi/14)`. -/
noncomputable def w14 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 14)

/-- The `k`-th Hückel eigenvalue of `C₁₄`, namely `2 cos (2πk/14)`. -/
noncomputable def C14eigval (k : Fin 14) : ℂ :=
  2 * (Real.cos (2 * Real.pi * k.val / 14) : ℝ)

/-- The `k`-th eigenvector of the adjacency matrix of `C₁₄`. -/
noncomputable def C14eigvec (k : Fin 14) : Fin 14 → ℂ := fun j => w14 ^ (j.val * k.val)

/-- The Fourier (Vandermonde) matrix diagonalising `C14adj`. -/
noncomputable def C14vand : Matrix (Fin 14) (Fin 14) ℂ :=
  Matrix.vandermonde (fun i : Fin 14 => w14 ^ i.val)

lemma w14_primitive : IsPrimitiveRoot w14 14 := by
  have h := Complex.isPrimitiveRoot_exp 14 (by norm_num)
  simpa [w14] using h

lemma w14_pow_14 : w14 ^ 14 = 1 := w14_primitive.pow_eq_one

lemma w14_ne_zero : w14 ≠ 0 := Complex.exp_ne_zero _

lemma w14_pow_congr {a b : ℕ} (h : a % 14 = b % 14) : w14 ^ a = w14 ^ b := by
  conv_lhs => rw [← Nat.div_add_mod a 14]
  conv_rhs => rw [← Nat.div_add_mod b 14]
  simp [pow_add, pow_mul, w14_pow_14, h]

lemma w14_pow_eq_exp (m : ℕ) :
    w14 ^ m = Complex.exp ((2 * Real.pi * m / 14 : ℝ) * Complex.I) := by
  rw [w14, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma w14_pow_add_pow (k : Fin 14) :
    w14 ^ k.val + w14 ^ (13 * k.val) = C14eigval k := by
  have h1 : w14 ^ (13 * k.val) * w14 ^ k.val = 1 := by
    rw [← pow_add, show 13 * k.val + k.val = 14 * k.val by ring, pow_mul, w14_pow_14, one_pow]
  have hinv : w14 ^ (13 * k.val) = (w14 ^ k.val)⁻¹ := eq_inv_of_mul_eq_one_left h1
  rw [hinv, w14_pow_eq_exp, ← Complex.exp_neg, C14eigval,
    show -((2 * Real.pi * k.val / 14 : ℝ) * Complex.I)
        = -((2 * Real.pi * k.val / 14 : ℝ) : ℂ) * Complex.I by ring,
    ← Complex.two_cos, Complex.ofReal_cos]

lemma C14adj_apply (i j : Fin 14) :
    C14adj i j = (if j = i + 1 then 1 else 0) + (if j = i - 1 then 1 else 0) := by
  have hadj : ∀ u v : Fin 14, ((cycleGraph 14).Adj u v ↔ (v = u + 1 ∨ v = u - 1)) := by decide
  have hne : ∀ u : Fin 14, (u + 1 : Fin 14) ≠ u - 1 := by decide
  rw [C14adj, SimpleGraph.adjMatrix_apply]
  by_cases h1 : j = i + 1
  · have h2 : j ≠ i - 1 := by rw [h1]; exact hne i
    rw [if_pos ((hadj i j).2 (Or.inl h1)), if_pos h1, if_neg h2]
    norm_num
  · by_cases h2 : j = i - 1
    · rw [if_pos ((hadj i j).2 (Or.inr h2)), if_neg h1, if_pos h2]
      norm_num
    · rw [if_neg (fun hA => ((hadj i j).1 hA).elim h1 h2), if_neg h1, if_neg h2]
      norm_num

lemma C14vand_apply (i j : Fin 14) : C14vand i j = w14 ^ (i.val * j.val) := by
  simp [C14vand, Matrix.vandermonde_apply, ← pow_mul]

lemma C14vand_succ (i k : Fin 14) : C14vand (i + 1) k = C14vand i k * w14 ^ k.val := by
  have hval : ∀ u : Fin 14, (u + 1 : Fin 14).val = (u.val + 1) % 14 := by decide
  rw [C14vand_apply, C14vand_apply, hval,
    w14_pow_congr (b := (i.val + 1) * k.val) ((Nat.mod_modEq (i.val + 1) 14).mul_right k.val),
    show (i.val + 1) * k.val = i.val * k.val + k.val by ring, pow_add]

lemma C14vand_pred (i k : Fin 14) : C14vand (i - 1) k = C14vand i k * w14 ^ (13 * k.val) := by
  have hval : ∀ u : Fin 14, (u - 1 : Fin 14).val = (u.val + 13) % 14 := by decide
  rw [C14vand_apply, C14vand_apply, hval,
    w14_pow_congr (b := (i.val + 13) * k.val) ((Nat.mod_modEq (i.val + 13) 14).mul_right k.val),
    show (i.val + 13) * k.val = i.val * k.val + 13 * k.val by ring, pow_add]

lemma C14adj_mul_vand : C14adj * C14vand = C14vand * Matrix.diagonal C14eigval := by
  ext i k
  rw [Matrix.mul_apply, Matrix.mul_diagonal]
  have hterm : ∀ j : Fin 14, C14adj i j * C14vand j k
      = (if j = i + 1 then C14vand j k else 0) + (if j = i - 1 then C14vand j k else 0) := by
    intro j
    rw [C14adj_apply]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ (i + 1) (fun j => C14vand j k),
    Finset.sum_ite_eq' Finset.univ (i - 1) (fun j => C14vand j k)]
  simp only [Finset.mem_univ, if_true]
  rw [C14vand_succ, C14vand_pred, ← mul_add, w14_pow_add_pow]

lemma C14vand_det_ne_zero : C14vand.det ≠ 0 := by
  rw [C14vand, Matrix.det_vandermonde_ne_zero_iff]
  intro a b hab
  exact Fin.ext (w14_primitive.pow_inj a.isLt b.isLt hab)

lemma C14vand_isUnit : IsUnit C14vand :=
  (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 C14vand_det_ne_zero)

lemma C14adj_charpoly :
    C14adj.charpoly = ∏ k : Fin 14, (X - C (C14eigval k)) := by
  obtain ⟨u, hu⟩ := C14vand_isUnit
  have hinv : (u⁻¹ : (Matrix (Fin 14) (Fin 14) ℂ)ˣ).val * C14adj * u.val
      = Matrix.diagonal C14eigval := by
    rw [mul_assoc, hu, C14adj_mul_vand, ← hu, ← mul_assoc]
    simp
  calc C14adj.charpoly
      = ((u⁻¹ : (Matrix (Fin 14) (Fin 14) ℂ)ˣ).val * C14adj * u.val).charpoly :=
        (Matrix.charpoly_units_conj' u C14adj).symm
    _ = (Matrix.diagonal C14eigval).charpoly := by rw [hinv]
    _ = ∏ k : Fin 14, (X - C (C14eigval k)) := Matrix.charpoly_diagonal _

lemma C14adj_spectrum : spectrum ℂ C14adj = {μ | ∃ k : Fin 14, μ = C14eigval k} := by
  ext μ
  rw [spectrum.mem_iff]
  have halg : algebraMap ℂ (Matrix (Fin 14) (Fin 14) ℂ) μ = Matrix.scalar (Fin 14) μ := rfl
  rw [halg, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not,
    ← Matrix.eval_charpoly, C14adj_charpoly]
  simp only [Polynomial.eval_prod, eval_sub, eval_X, eval_C, Set.mem_setOf_eq]
  constructor
  · intro h
    obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.1 h
    exact ⟨k, sub_eq_zero.1 hk⟩
  · rintro ⟨k, hk⟩
    exact Finset.prod_eq_zero (f := fun k => μ - C14eigval k) (Finset.mem_univ k)
      (by simp [hk])

lemma C14adj_mulVec_eigvec (k : Fin 14) :
    C14adj *ᵥ C14eigvec k = C14eigval k • C14eigvec k := by
  funext i
  have hv : ∀ j : Fin 14, C14eigvec k j = C14vand j k := fun j => by
    rw [C14vand_apply, C14eigvec]
  calc (C14adj *ᵥ C14eigvec k) i
      = ∑ j, C14adj i j * C14vand j k := by
        simp only [Matrix.mulVec, dotProduct, hv]
    _ = (C14adj * C14vand) i k := (Matrix.mul_apply).symm
    _ = (C14vand * Matrix.diagonal C14eigval) i k := by rw [C14adj_mul_vand]
    _ = C14vand i k * C14eigval k := by rw [Matrix.mul_diagonal]
    _ = (C14eigval k • C14eigvec k) i := by
        simp only [Pi.smul_apply, smul_eq_mul, hv i]; ring

lemma C14eigvec_ne_zero (k : Fin 14) : C14eigvec k ≠ 0 := by
  intro hzero
  have h := congrFun hzero 0
  simp [C14eigvec] at h

/-- **Hückel theory for the C₁₄ annulene ring.**
The adjacency (Hückel) matrix of the cycle graph `C₁₄` has eigenvalues `2 cos (2πk/14)`,
`k = 0, …, 13`:
* the explicit vector `j ↦ exp(2πi·jk/14)` is a nonzero eigenvector with
  eigenvalue `2 cos (2πk/14)`;
* the characteristic polynomial factors as `∏ k, (X - 2 cos (2πk/14))`, so these are the
  eigenvalues with multiplicity;
* the spectrum is exactly the set of these 14 numbers. -/
theorem huckel_C14 :
    (∀ k : Fin 14, C14adj *ᵥ C14eigvec k
        = (2 * (Real.cos (2 * Real.pi * k.val / 14) : ℝ) : ℂ) • C14eigvec k
      ∧ C14eigvec k ≠ 0) ∧
    C14adj.charpoly
        = ∏ k : Fin 14, (X - C ((2 * (Real.cos (2 * Real.pi * k.val / 14) : ℝ) : ℂ))) ∧
    spectrum ℂ C14adj
        = {μ : ℂ | ∃ k : Fin 14, μ = (2 * (Real.cos (2 * Real.pi * k.val / 14) : ℝ) : ℂ)} :=
  ⟨fun k => ⟨C14adj_mulVec_eigvec k, C14eigvec_ne_zero k⟩, C14adj_charpoly, C14adj_spectrum⟩

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

