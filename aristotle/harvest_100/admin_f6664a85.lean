/-
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The Hückel model for the annulene `C₁₈` uses the adjacency matrix of the cycle
graph `C₁₈`.  We show that its eigenvalues are exactly the `18` numbers
`2 cos (2πk/18)`, `k = 0, …, 17`.
-/

namespace Chem

open Complex Matrix

/-- The adjacency matrix of the cycle graph `C₁₈` on the vertex set `Fin 18`:
vertices `i` and `j` are adjacent iff they are consecutive modulo `18`. -/
noncomputable def C18adj : Matrix (Fin 18) (Fin 18) ℂ :=
  Matrix.of fun i j => if j.val = (i.val + 1) % 18 ∨ i.val = (j.val + 1) % 18 then 1 else 0

/-- The primitive 18-th root of unity `exp (2πi/18)`. -/
noncomputable def zeta : ℂ := Complex.exp (2 * Real.pi * I / 18)

/-- The `k`-th Hückel eigenvalue, written in terms of `zeta`. -/
noncomputable def lam (k : Fin 18) : ℂ := zeta ^ (k : ℕ) + (zeta ^ (k : ℕ)) ^ 17

/-- The Vandermonde-type matrix whose `k`-th column is the eigenvector for `lam k`. -/
noncomputable def V : Matrix (Fin 18) (Fin 18) ℂ :=
  (Matrix.vandermonde fun k : Fin 18 => zeta ^ (k : ℕ))ᵀ

lemma zeta_primitive : IsPrimitiveRoot zeta 18 := by
  have := Complex.isPrimitiveRoot_exp 18 (by norm_num)
  simpa [zeta] using this

lemma zeta_pow_eighteen : zeta ^ 18 = 1 := zeta_primitive.pow_eq_one

lemma zeta_pow (k : ℕ) : zeta ^ k = Complex.exp ((2 * Real.pi * k / 18 : ℝ) * I) := by
  rw [zeta, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma zeta_pow_pow_eighteen (k : ℕ) : (zeta ^ k) ^ 18 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, zeta_pow_eighteen, one_pow]

/-- The eigenvalue `lam k` really is `2 cos (2πk/18)`. -/
lemma lam_eq (k : ℕ) :
    ((2 * Real.cos (2 * Real.pi * k / 18) : ℝ) : ℂ) = zeta ^ k + (zeta ^ k) ^ 17 := by
  have h18 : (zeta ^ k) ^ 18 = 1 := zeta_pow_pow_eighteen k
  have hne : zeta ^ k ≠ 0 := by
    intro h
    rw [h] at h18
    simp at h18
  have h17 : (zeta ^ k) ^ 17 = (zeta ^ k)⁻¹ := by
    field_simp
    linear_combination h18
  rw [h17, zeta_pow k, ← Complex.exp_neg]
  rw [Complex.exp_mul_I,
    show -((2 * Real.pi * k / 18 : ℝ) * I) = (-(2 * Real.pi * k / 18 : ℝ)) * I by ring,
    Complex.exp_mul_I]
  push_cast
  simp [Complex.cos_neg, Complex.sin_neg]
  ring

/-- The fundamental computation: the geometric vector `j ↦ z ^ j` is an eigenvector of the
cycle adjacency matrix whenever `z ^ 18 = 1`. -/
lemma key (z : ℂ) (hz : z ^ 18 = 1) (i : Fin 18) :
    ∑ j : Fin 18, C18adj i j * z ^ j.val = (z + z ^ 17) * z ^ i.val := by
  fin_cases i <;>
    simp [C18adj, Fin.sum_univ_succ] <;>
    first
      | ring1
      | linear_combination -hz
      | linear_combination -z * hz
      | linear_combination -z ^ 2 * hz
      | linear_combination -z ^ 3 * hz
      | linear_combination -z ^ 4 * hz
      | linear_combination -z ^ 5 * hz
      | linear_combination -z ^ 6 * hz
      | linear_combination -z ^ 7 * hz
      | linear_combination -z ^ 8 * hz
      | linear_combination -z ^ 9 * hz
      | linear_combination -z ^ 10 * hz
      | linear_combination -z ^ 11 * hz
      | linear_combination -z ^ 12 * hz
      | linear_combination -z ^ 13 * hz
      | linear_combination -z ^ 14 * hz
      | linear_combination -z ^ 15 * hz
      | linear_combination (-1 - z ^ 16) * hz

lemma C18adj_mulVec (z : ℂ) (hz : z ^ 18 = 1) :
    C18adj *ᵥ (fun j : Fin 18 => z ^ j.val) = (z + z ^ 17) • (fun j : Fin 18 => z ^ j.val) := by
  funext i
  simpa [Matrix.mulVec, dotProduct] using key z hz i

lemma C18adj_mul_V : C18adj * V = V * Matrix.diagonal lam := by
  ext i k
  have h := key (zeta ^ (k : ℕ)) (zeta_pow_pow_eighteen k) i
  simp [Matrix.mul_apply, V, Matrix.vandermonde, Matrix.diagonal, lam, ← pow_mul,
    Finset.sum_ite_eq'] at h ⊢
  simpa [mul_comm] using h

lemma V_det_ne_zero : V.det ≠ 0 := by
  rw [V, Matrix.det_transpose, Matrix.det_vandermonde]
  refine Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j hj => ?_
  simp only [Finset.mem_Ioi] at hj
  refine sub_ne_zero.2 fun h => ?_
  have := zeta_primitive.pow_inj j.isLt i.isLt h
  exact absurd this (by omega)

lemma det_sub_smul (μ : ℂ) :
    (C18adj - μ • (1 : Matrix (Fin 18) (Fin 18) ℂ)).det = ∏ k : Fin 18, (lam k - μ) := by
  have hcomm : (C18adj - μ • (1 : Matrix (Fin 18) (Fin 18) ℂ)) * V
      = V * (Matrix.diagonal lam - μ • (1 : Matrix (Fin 18) (Fin 18) ℂ)) := by
    rw [sub_mul, mul_sub, C18adj_mul_V, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  have hdet := congrArg Matrix.det hcomm
  rw [Matrix.det_mul, Matrix.det_mul] at hdet
  have h2 : (Matrix.diagonal lam - μ • (1 : Matrix (Fin 18) (Fin 18) ℂ))
      = Matrix.diagonal fun k => lam k - μ := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.diagonal, h]
  rw [h2, Matrix.det_diagonal] at hdet
  refine mul_right_cancel₀ V_det_ne_zero ?_
  rw [hdet, mul_comm]

/-- **Hückel spectrum of `C₁₈`.** A complex number `μ` is an eigenvalue of the adjacency
matrix of the cycle graph `C₁₈` if and only if `μ = 2 cos (2πk/18)` for some `k < 18`. -/
theorem huckel_C18 (μ : ℂ) :
    (∃ v : Fin 18 → ℂ, v ≠ 0 ∧ C18adj *ᵥ v = μ • v) ↔
      ∃ k : ℕ, k < 18 ∧ μ = ((2 * Real.cos (2 * Real.pi * k / 18) : ℝ) : ℂ) := by
  constructor
  · rintro ⟨v, hv, hveq⟩
    have h0 : (C18adj - μ • (1 : Matrix (Fin 18) (Fin 18) ℂ)) *ᵥ v = 0 := by
      rw [Matrix.sub_mulVec, hveq, Matrix.smul_mulVec, Matrix.one_mulVec, sub_self]
    have hdet : (C18adj - μ • (1 : Matrix (Fin 18) (Fin 18) ℂ)).det = 0 :=
      Matrix.exists_mulVec_eq_zero_iff.1 ⟨v, hv, h0⟩
    rw [det_sub_smul] at hdet
    obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.1 hdet
    refine ⟨k, k.isLt, ?_⟩
    rw [lam_eq]
    exact (sub_eq_zero.1 hk).symm
  · rintro ⟨k, hk, rfl⟩
    refine ⟨fun j : Fin 18 => (zeta ^ k) ^ j.val, ?_, ?_⟩
    · intro h
      have := congrFun h (0 : Fin 18)
      simp at this
    · rw [C18adj_mulVec _ (zeta_pow_pow_eighteen k), lam_eq]

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

