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
-/

open scoped Matrix
open Complex

namespace Chem

/-- The adjacency matrix (Hückel matrix, with `α = 0`, `β = 1`) of the cycle graph `C₁₀`. -/
noncomputable def C10 : Matrix (Fin 10) (Fin 10) ℂ :=
  (SimpleGraph.cycleGraph 10).adjMatrix ℂ

/-- A primitive 10-th root of unity. -/
noncomputable def zeta10 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 10)

/-- The candidate eigenvector for index `k` : `j ↦ ζ ^ (k * j)`. -/
noncomputable def zk (k : Fin 10) : ℂ := zeta10 ^ (k : ℕ)

/-- The `k`-th Hückel eigenvalue `2 cos (2πk/10)`. -/
noncomputable def mu (k : Fin 10) : ℂ := ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 10) : ℝ) : ℂ)

/-- The matrix of eigenvectors: `F i k = (ζ^k)^i`. -/
noncomputable def F : Matrix (Fin 10) (Fin 10) ℂ := Matrix.of fun i k => (zk k) ^ (i : ℕ)

lemma zeta10_isPrimitiveRoot : IsPrimitiveRoot zeta10 10 := by
  simpa [zeta10] using Complex.isPrimitiveRoot_exp 10 (by norm_num)

lemma zeta10_pow_ten : zeta10 ^ 10 = 1 := zeta10_isPrimitiveRoot.pow_eq_one

lemma zeta10_ne_zero : zeta10 ≠ 0 := by
  simp [zeta10, Complex.exp_ne_zero]

lemma zk_ne_zero (k : Fin 10) : zk k ≠ 0 := pow_ne_zero _ zeta10_ne_zero

lemma zk_pow_ten (k : Fin 10) : (zk k) ^ 10 = 1 := by
  rw [zk, ← pow_mul, mul_comm, pow_mul, zeta10_pow_ten, one_pow]

lemma zk_injective : Function.Injective zk :=
  fun a b h => Fin.ext (zeta10_isPrimitiveRoot.pow_inj a.isLt b.isLt h)

lemma zk_add_inv (k : Fin 10) : zk k + (zk k)⁻¹ = mu k := by
  have h1 : zk k = Complex.exp (((2 * Real.pi * (k : ℕ) / 10 : ℝ) : ℂ) * Complex.I) := by
    rw [zk, zeta10, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [h1, ← Complex.exp_neg, mu, Complex.ofReal_mul, Complex.ofReal_cos, Complex.cos]
  push_cast
  ring_nf

lemma zk_inv_eq (k : Fin 10) : (zk k)⁻¹ = (zk k) ^ 9 :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact zk_pow_ten k)

/-- The cyclic three-term recurrence satisfied by the powers of a 10-th root of unity. -/
lemma pow_shift_eq (z : ℂ) (h10 : z ^ 10 = 1) (i : Fin 10) :
    z ^ ((i - 1 : Fin 10) : ℕ) + z ^ ((i + 1 : Fin 10) : ℕ) = z ^ (i : ℕ) * (z + z ^ 9) := by
  fin_cases i <;> norm_num [Fin.sub_def, Fin.add_def] <;>
    first
      | ring1
      | linear_combination (-1 : ℂ) * h10
      | linear_combination (-z) * h10
      | linear_combination (-z ^ 2) * h10
      | linear_combination (-z ^ 3) * h10
      | linear_combination (-z ^ 4) * h10
      | linear_combination (-z ^ 5) * h10
      | linear_combination (-z ^ 6) * h10
      | linear_combination (-z ^ 7) * h10
      | linear_combination (-1 - z ^ 8) * h10

lemma C10_mulVec (v : Fin 10 → ℂ) (i : Fin 10) : (C10 *ᵥ v) i = v (i - 1) + v (i + 1) := by
  fin_cases i <;>
    simp +decide [C10, SimpleGraph.adjMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      SimpleGraph.cycleGraph_adj, show (-1 : Fin 10) = 9 from by decide] <;> ring

lemma C10_mul_F : C10 * F = F * Matrix.diagonal mu := by
  ext i k
  have hL : (C10 * F) i k = (C10 *ᵥ fun j => F j k) i := rfl
  rw [hL, C10_mulVec, Matrix.mul_diagonal]
  simpa [F, ← zk_add_inv k, zk_inv_eq k] using pow_shift_eq (zk k) (zk_pow_ten k) i

lemma det_F_ne_zero : F.det ≠ 0 := by
  have hT : Fᵀ = Matrix.vandermonde zk := by
    ext k i; simp [F, Matrix.vandermonde]
  rw [← Matrix.det_transpose, hT]
  exact Matrix.det_vandermonde_ne_zero_iff.mpr zk_injective

lemma det_sub_smul (lam : ℂ) :
    (C10 - lam • (1 : Matrix (Fin 10) (Fin 10) ℂ)).det * F.det
      = F.det * ∏ k : Fin 10, (mu k - lam) := by
  have hmul : (C10 - lam • (1 : Matrix (Fin 10) (Fin 10) ℂ)) * F
      = F * Matrix.diagonal fun k => mu k - lam := by
    have hd : (Matrix.diagonal fun k => mu k - lam)
        = Matrix.diagonal mu - lam • (1 : Matrix (Fin 10) (Fin 10) ℂ) := by
      ext i j
      by_cases h : i = j <;> simp [Matrix.diagonal, h]
    rw [hd, sub_mul, mul_sub, C10_mul_F, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  have := congrArg Matrix.det hmul
  rwa [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal] at this

/-- The explicit Hückel eigenvector for index `k`: the vertex `i` gets amplitude `ζ^(k i)`,
with eigenvalue `2 cos (2πk/10)`. -/
lemma C10_mulVec_eigenvector (k : Fin 10) :
    C10 *ᵥ (fun i : Fin 10 => zk k ^ (i : ℕ)) = mu k • fun i : Fin 10 => zk k ^ (i : ℕ) := by
  funext i
  rw [C10_mulVec]
  simpa [mul_comm, ← zk_add_inv k, zk_inv_eq k] using pow_shift_eq (zk k) (zk_pow_ten k) i

/-- **The Hückel spectrum of `C₁₀`.**  The eigenvalues of the adjacency matrix of the cycle
graph on 10 vertices are exactly the numbers `2 cos (2πk/10)`, `k = 0, …, 9`. -/
theorem huckel_C10 :
    {lam : ℂ | ∃ v : Fin 10 → ℂ, v ≠ 0 ∧ (SimpleGraph.cycleGraph 10).adjMatrix ℂ *ᵥ v = lam • v}
      = {lam : ℂ | ∃ k : Fin 10, lam = ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 10) : ℝ) : ℂ)} := by
  ext lam
  simp only [Set.mem_setOf_eq]
  have hiff : (∃ v : Fin 10 → ℂ, v ≠ 0 ∧
        (SimpleGraph.cycleGraph 10).adjMatrix ℂ *ᵥ v = lam • v)
      ↔ (C10 - lam • (1 : Matrix (Fin 10) (Fin 10) ℂ)).det = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    constructor
    · rintro ⟨v, hv, heq⟩
      refine ⟨v, hv, ?_⟩
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, ← heq]
      simp [C10]
    · rintro ⟨v, hv, heq⟩
      refine ⟨v, hv, ?_⟩
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at heq
      simpa [C10] using heq
  rw [hiff]
  have hdet := det_sub_smul lam
  constructor
  · intro h
    rw [h, zero_mul] at hdet
    have : ∏ k : Fin 10, (mu k - lam) = 0 :=
      (mul_eq_zero.mp hdet.symm).resolve_left det_F_ne_zero
    obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.mp this
    exact ⟨k, (sub_eq_zero.mp hk).symm⟩
  · rintro ⟨k, hk⟩
    have hzero : ∏ j : Fin 10, (mu j - lam) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ k) (by rw [hk]; simp [mu])
    rw [hzero, mul_zero] at hdet
    exact (mul_eq_zero.mp hdet).resolve_right det_F_ne_zero

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

