/-!
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Statement: The adjacency eigenvalues of the cycle graph C_19 are 2·cos(2πk/19) for k=0..18.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Chem

open Complex Matrix Finset

/-- A primitive 19-th root of unity. -/
noncomputable def zeta19 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 19)

lemma isPrimitiveRoot_zeta19 : IsPrimitiveRoot zeta19 19 := by
  have h := Complex.isPrimitiveRoot_exp 19 (by norm_num)
  simpa [zeta19] using h

lemma zeta19_pow_19 : zeta19 ^ 19 = 1 := isPrimitiveRoot_zeta19.pow_eq_one

lemma zeta19_ne_zero : zeta19 ≠ 0 := by
  simp [zeta19, Complex.exp_ne_zero]

lemma zeta19_pow_mod (m : ℕ) : zeta19 ^ m = zeta19 ^ (m % 19) := by
  conv_lhs => rw [← Nat.div_add_mod m 19]
  rw [pow_add, pow_mul, zeta19_pow_19, one_pow, one_mul]

lemma zeta19_pow_congr {m n : ℕ} (h : m ≡ n [MOD 19]) : zeta19 ^ m = zeta19 ^ n := by
  rw [zeta19_pow_mod m, zeta19_pow_mod n, h]

/-- The `k`-th Hückel eigenvalue `2 cos (2πk/19)` of the cycle `C₁₉`. -/
noncomputable def lam19 (k : ℕ) : ℂ := (2 * Real.cos (2 * Real.pi * k / 19) : ℝ)

lemma zeta19_pow_add_inv (k : ℕ) :
    zeta19 ^ k + (zeta19 ^ k)⁻¹ = lam19 k := by
  have hk : zeta19 ^ k = Complex.exp (((2 * Real.pi * k / 19 : ℝ) : ℂ) * Complex.I) := by
    rw [zeta19, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hk, ← Complex.exp_neg, lam19, Complex.ofReal_mul, Complex.ofReal_cos, Complex.cos]
  push_cast
  rw [neg_mul]
  ring

/-- The discrete Fourier matrix. -/
noncomputable def P19 : Matrix (Fin 19) (Fin 19) ℂ :=
  Matrix.of fun j k => zeta19 ^ (j.val * k.val)

/-- The conjugate Fourier matrix (the inverse of `P19` up to the factor `19`). -/
noncomputable def Q19 : Matrix (Fin 19) (Fin 19) ℂ :=
  Matrix.of fun j k => (zeta19⁻¹) ^ (j.val * k.val)

/-- The diagonal matrix of Hückel eigenvalues. -/
noncomputable def D19 : Matrix (Fin 19) (Fin 19) ℂ :=
  Matrix.diagonal fun k : Fin 19 => lam19 k.val

lemma geom_sum_19 {z : ℂ} (h1 : z ^ 19 = 1) (h2 : z ≠ 1) :
    ∑ i ∈ Finset.range 19, z ^ i = 0 := by
  rw [geom_sum_eq h2 19, h1, sub_self, zero_div]

lemma P19_mul_Q19 : P19 * Q19 = (19 : ℂ) • (1 : Matrix (Fin 19) (Fin 19) ℂ) := by
  ext j l
  rw [Matrix.mul_apply]
  obtain ⟨z, hz⟩ : ∃ z : ℂ, z = zeta19 ^ j.val * (zeta19⁻¹) ^ l.val := ⟨_, rfl⟩
  have hterm : ∀ k : Fin 19, P19 j k * Q19 k l = z ^ k.val := by
    intro k
    simp only [P19, Q19, Matrix.of_apply, hz, mul_pow, ← pow_mul]
    rw [mul_comm k.val l.val]
  rw [Finset.sum_congr rfl (fun k _ => hterm k)]
  rw [Fin.sum_univ_eq_sum_range (fun i => z ^ i) 19]
  by_cases hjl : j = l
  · subst hjl
    have hz1 : z = 1 := by
      rw [hz, ← mul_pow, mul_inv_cancel₀ zeta19_ne_zero, one_pow]
    simp [hz1]
  · have hzne : z ≠ 1 := by
      intro h
      apply hjl
      have h' : zeta19 ^ j.val = zeta19 ^ l.val := by
        rw [hz, inv_pow, mul_inv_eq_one₀ (pow_ne_zero _ zeta19_ne_zero)] at h
        exact h
      exact Fin.ext (isPrimitiveRoot_zeta19.pow_inj j.isLt l.isLt h')
    have hz19 : z ^ 19 = 1 := by
      rw [hz, mul_pow, ← pow_mul, ← pow_mul, mul_comm j.val 19, mul_comm l.val 19,
        pow_mul, pow_mul, zeta19_pow_19, inv_pow, zeta19_pow_19]
      simp
    rw [geom_sum_19 hz19 hzne]
    simp [hjl]

lemma A19_mul_P19 :
    (SimpleGraph.cycleGraph 19).adjMatrix ℂ * P19 = P19 * D19 := by
  ext i k
  have hmul : ((SimpleGraph.cycleGraph 19).adjMatrix ℂ * P19) i k
      = ((SimpleGraph.cycleGraph 19).adjMatrix ℂ).mulVec (fun j => P19 j k) i := by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [hmul, SimpleGraph.adjMatrix_mulVec_apply,
    (SimpleGraph.cycleGraph_neighborFinset (n := 17) (v := i))]
  have hne : ∀ j : Fin 19, j - 1 ≠ j + 1 := by decide
  rw [Finset.sum_pair (hne i)]
  -- right-hand side
  rw [D19, Matrix.mul_diagonal]
  simp only [P19, Matrix.of_apply]
  -- exponent computations
  have hplus : ((i + 1 : Fin 19)).val * k.val ≡ i.val * k.val + k.val [MOD 19] := by
    have h1 : ((i + 1 : Fin 19)).val = (i.val + 1) % 19 := by
      rw [Fin.val_add]
      rfl
    calc ((i + 1 : Fin 19)).val * k.val = ((i.val + 1) % 19) * k.val := by rw [h1]
      _ ≡ (i.val + 1) * k.val [MOD 19] := Nat.ModEq.mul_right _ (Nat.mod_modEq _ _)
      _ = i.val * k.val + k.val := by ring
  have hminus : ((i - 1 : Fin 19)).val * k.val ≡ i.val * k.val + 18 * k.val [MOD 19] := by
    have h1 : ((i - 1 : Fin 19)).val = (18 + i.val) % 19 := by
      simp [Fin.sub_def]
    calc ((i - 1 : Fin 19)).val * k.val = ((18 + i.val) % 19) * k.val := by
          rw [h1]
      _ ≡ (18 + i.val) * k.val [MOD 19] := Nat.ModEq.mul_right _ (Nat.mod_modEq _ _)
      _ = i.val * k.val + 18 * k.val := by ring
  rw [zeta19_pow_congr hplus, zeta19_pow_congr hminus]
  have h18 : zeta19 ^ (18 * k.val) = (zeta19 ^ k.val)⁻¹ := by
    refine (inv_eq_of_mul_eq_one_right ?_).symm
    rw [← pow_add, show k.val + 18 * k.val = 19 * k.val by ring, pow_mul, zeta19_pow_19,
      one_pow]
  rw [pow_add, pow_add, h18, ← zeta19_pow_add_inv k.val]
  ring

lemma spectrum_diagonal19 (d : Fin 19 → ℂ) :
    spectrum ℂ (Matrix.diagonal d) = Set.range d := by
  ext mu
  have hmat : algebraMap ℂ (Matrix (Fin 19) (Fin 19) ℂ) mu - Matrix.diagonal d
      = Matrix.diagonal (fun i => mu - d i) := by
    rw [Matrix.algebraMap_eq_diagonal, ← Matrix.diagonal_sub]
    rfl
  simp only [Set.mem_range, spectrum.mem_iff, hmat, Matrix.isUnit_iff_isUnit_det,
    Matrix.det_diagonal, isUnit_iff_ne_zero, not_not, Finset.prod_eq_zero_iff,
    Finset.mem_univ, true_and, sub_eq_zero, ne_eq]
  constructor
  · rintro ⟨i, hi⟩; exact ⟨i, hi.symm⟩
  · rintro ⟨i, hi⟩; exact ⟨i, hi.symm⟩

lemma isUnit_P19 : IsUnit P19 := by
  refine IsUnit.of_mul_eq_one ((19 : ℂ)⁻¹ • Q19) ?_
  rw [Matrix.mul_smul, P19_mul_Q19, smul_smul]
  norm_num

/-- The explicit Hückel molecular orbitals: the vector `j ↦ ζ^(jk)` (with `ζ = exp (2πi/19)`)
is an eigenvector of the adjacency matrix of `C₁₉` with eigenvalue `2 cos (2πk/19)`. -/
theorem huckel_C19_eigenvector (k : Fin 19) :
    ((SimpleGraph.cycleGraph 19).adjMatrix ℂ).mulVec (fun j : Fin 19 => zeta19 ^ (j.val * k.val))
      = lam19 k.val • fun j : Fin 19 => zeta19 ^ (j.val * k.val) := by
  funext i
  have h : ((SimpleGraph.cycleGraph 19).adjMatrix ℂ * P19) i k = (P19 * D19) i k :=
    congrFun (congrFun A19_mul_P19 i) k
  rw [D19, Matrix.mul_diagonal] at h
  simp only [Matrix.mul_apply, P19, Matrix.of_apply] at h
  simpa [Matrix.mulVec, dotProduct, mul_comm] using h

/-- **Hückel theory for the C₁₉ cycle**: the adjacency eigenvalues of the cycle graph `C₁₉`
are exactly `2 cos (2πk/19)` for `k = 0, …, 18`. -/
theorem huckel_C19 :
    spectrum ℂ ((SimpleGraph.cycleGraph 19).adjMatrix ℂ) =
      {z : ℂ | ∃ k : ℕ, k < 19 ∧ z = (2 * Real.cos (2 * Real.pi * k / 19) : ℝ)} := by
  obtain ⟨u, hu⟩ := isUnit_P19
  have hconj : (SimpleGraph.cycleGraph 19).adjMatrix ℂ
      = (u : Matrix (Fin 19) (Fin 19) ℂ) * D19 * ((u⁻¹ : (Matrix (Fin 19) (Fin 19) ℂ)ˣ) :
        Matrix (Fin 19) (Fin 19) ℂ) := by
    have h : (u : Matrix (Fin 19) (Fin 19) ℂ) * D19
        = (SimpleGraph.cycleGraph 19).adjMatrix ℂ * (u : Matrix (Fin 19) (Fin 19) ℂ) := by
      rw [hu, ← A19_mul_P19]
    rw [h, mul_assoc, Units.mul_inv, mul_one]
  rw [hconj, spectrum.units_conjugate, D19, spectrum_diagonal19]
  ext z
  simp only [Set.mem_range, Set.mem_setOf_eq, lam19]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k.val, k.isLt, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, hk⟩, rfl⟩

end Chem

