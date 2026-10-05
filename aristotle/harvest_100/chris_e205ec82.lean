import Mathlib

/-!
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix SimpleGraph Finset

/-- The adjacency matrix of the cycle graph `C₁₃` (the Hückel matrix of the
`C₁₃` carbon ring, in units where `α = 0` and `β = 1`). -/
noncomputable def C13 : Matrix (Fin 13) (Fin 13) ℂ :=
  (SimpleGraph.cycleGraph 13).adjMatrix ℂ

/-- A primitive 13-th root of unity. -/
noncomputable def om : ℂ := Complex.exp (2 * Real.pi * Complex.I / 13)

lemma om_primitive : IsPrimitiveRoot om 13 := by
  have h := Complex.isPrimitiveRoot_exp 13 (by norm_num)
  simpa [om] using h

lemma om_pow13 : om ^ 13 = 1 := om_primitive.pow_eq_one

lemma om_ne_zero : om ≠ 0 := Complex.exp_ne_zero _

/-- The 13-th root of unity appearing in the `k`-th eigenvector. -/
noncomputable def zeta (k : Fin 13) : ℂ := om ^ (k : ℕ)

lemma zeta_pow13 (k : Fin 13) : zeta k ^ 13 = 1 := by
  rw [zeta, ← pow_mul, mul_comm, pow_mul, om_pow13, one_pow]

lemma zeta_ne_zero (k : Fin 13) : zeta k ≠ 0 := pow_ne_zero _ om_ne_zero

lemma pow_mod13 {z : ℂ} (hz : z ^ 13 = 1) (x : ℕ) : z ^ (x % 13) = z ^ x := by
  conv_rhs => rw [← Nat.div_add_mod x 13]
  rw [pow_add, pow_mul, hz, one_pow, one_mul]

lemma zeta_eq_exp (k : Fin 13) :
    zeta k = Complex.exp (((2 * Real.pi * (k : ℕ) / 13 : ℝ) : ℂ) * Complex.I) := by
  rw [zeta, om, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The `k`-th eigenvector of the Hückel matrix. -/
noncomputable def vec (k : Fin 13) : Fin 13 → ℂ := fun j => zeta k ^ (j : ℕ)

/-- The `k`-th Hückel eigenvalue, `2 cos (2πk/13)`. -/
noncomputable def eval13 (k : Fin 13) : ℂ := (2 * Real.cos (2 * Real.pi * (k : ℕ) / 13) : ℝ)

lemma zeta_pow_twelve_add (k : Fin 13) : zeta k ^ 12 + zeta k = eval13 k := by
  have hz0 : zeta k ≠ 0 := zeta_ne_zero k
  have h12 : zeta k ^ 12 = (zeta k)⁻¹ := by
    field_simp
    linear_combination zeta_pow13 k
  rw [eval13, h12, zeta_eq_exp, ← Complex.exp_neg]
  push_cast
  rw [Complex.two_cos, neg_mul, add_comm]

lemma sum_adj (f : Fin 13 → ℂ) (j : Fin 13) :
    ∑ l, C13 j l * f l = f (j - 1) + f (j + 1) := by
  have hne : (j : Fin 13) - 1 ≠ j + 1 := by revert j; decide
  have h : ∑ l, C13 j l * f l = (C13 *ᵥ f) j := rfl
  rw [h, C13, SimpleGraph.adjMatrix_mulVec_apply, cycleGraph_neighborFinset,
    Finset.sum_pair hne]

lemma vec_succ (k j : Fin 13) : vec k (j + 1) = zeta k * vec k j := by
  have hval : ((j + 1 : Fin 13) : ℕ) = ((j : ℕ) + 1) % 13 := by simp [Fin.val_add]
  rw [vec, vec, hval, pow_mod13 (zeta_pow13 k), pow_succ]
  ring

lemma vec_pred (k j : Fin 13) : vec k (j - 1) = zeta k ^ 12 * vec k j := by
  have hval : ((j - 1 : Fin 13) : ℕ) = ((j : ℕ) + 12) % 13 := by
    simp [Fin.sub_def, Nat.add_comm]
  rw [vec, vec, hval, pow_mod13 (zeta_pow13 k), pow_add]
  ring

lemma C13_mulVec_vec (k : Fin 13) : C13 *ᵥ vec k = eval13 k • vec k := by
  funext j
  have h : (C13 *ᵥ vec k) j = ∑ l, C13 j l * vec k l := rfl
  rw [h, sum_adj, vec_pred, vec_succ, Pi.smul_apply, smul_eq_mul,
    ← zeta_pow_twelve_add k]
  ring

lemma vec_ne_zero (k : Fin 13) : vec k ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [vec] at h0

/-- The (unnormalized) discrete Fourier matrix, whose columns are the eigenvectors. -/
noncomputable def U : Matrix (Fin 13) (Fin 13) ℂ := fun j k => vec k j

/-- The inverse of the discrete Fourier matrix. -/
noncomputable def V : Matrix (Fin 13) (Fin 13) ℂ := fun k j => (13 : ℂ)⁻¹ * (vec k j)⁻¹

lemma U_apply (j k : Fin 13) : U j k = (om ^ (j : ℕ)) ^ (k : ℕ) := by
  rw [U, vec, zeta, ← pow_mul, ← pow_mul, Nat.mul_comm]

lemma U_mul_V : U * V = 1 := by
  ext j j'
  rw [Matrix.mul_apply]
  set x : ℂ := om ^ (j : ℕ) * (om ^ (j' : ℕ))⁻¹ with hx
  have hterm : ∀ k : Fin 13, U j k * V k j' = (13 : ℂ)⁻¹ * x ^ (k : ℕ) := by
    intro k
    rw [U_apply, V, vec, zeta, ← pow_mul, ← pow_mul, Nat.mul_comm (k : ℕ) (j' : ℕ), hx,
      mul_pow, inv_pow]
    ring
  rw [Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.mul_sum]
  have hsum : ∑ k : Fin 13, x ^ (k : ℕ) = ∑ k ∈ Finset.range 13, x ^ k :=
    Fin.sum_univ_eq_sum_range (fun k => x ^ k) 13
  rw [hsum]
  by_cases hjj : j = j'
  · subst hjj
    have hx1 : x = 1 := by
      rw [hx, mul_inv_cancel₀ (pow_ne_zero _ om_ne_zero)]
    rw [hx1]
    simp [Matrix.one_apply_eq]
  · have hx1 : x ≠ 1 := by
      intro h
      apply hjj
      have h' : om ^ (j : ℕ) = om ^ (j' : ℕ) := by
        rw [hx, ← div_eq_mul_inv, div_eq_one_iff_eq (pow_ne_zero _ om_ne_zero)] at h
        exact h
      exact Fin.ext (om_primitive.pow_inj j.isLt j'.isLt h')
    have hpow : ∀ m : ℕ, (om ^ m) ^ 13 = 1 := by
      intro m
      rw [← pow_mul, Nat.mul_comm, pow_mul, om_pow13, one_pow]
    have hx13 : x ^ 13 = 1 := by
      rw [hx, mul_pow, inv_pow, hpow, hpow, inv_one, mul_one]
    rw [geom_sum_eq hx1 13, hx13]
    simp [Matrix.one_apply_ne hjj]

lemma V_mul_U : V * U = 1 := mul_eq_one_comm.mp U_mul_V

lemma C13_mul_U : C13 * U = U * Matrix.diagonal eval13 := by
  ext j k
  rw [Matrix.mul_apply, Matrix.mul_diagonal]
  have h : ∑ l, C13 j l * U l k = (C13 *ᵥ vec k) j := rfl
  rw [h, C13_mulVec_vec, Pi.smul_apply, smul_eq_mul, U, mul_comm]

/-- **Hückel theory for the `C₁₃` ring.**  A complex number `μ` is an eigenvalue of the
adjacency (Hückel) matrix of the cycle graph `C₁₃` if and only if it is of the form
`2 * cos (2 * π * k / 13)` for some `k = 0, 1, …, 12`. -/
theorem huckel_C13 (μ : ℂ) :
    (∃ v : Fin 13 → ℂ, v ≠ 0 ∧ C13 *ᵥ v = μ • v) ↔
      ∃ k : ℕ, k < 13 ∧ μ = (2 * Real.cos (2 * Real.pi * k / 13) : ℝ) := by
  constructor
  · rintro ⟨v, hv0, hv⟩
    set w : Fin 13 → ℂ := V *ᵥ v with hw
    have hUw : U *ᵥ w = v := by
      rw [hw, Matrix.mulVec_mulVec, U_mul_V, Matrix.one_mulVec]
    have hw0 : w ≠ 0 := by
      intro h
      apply hv0
      rw [← hUw, h, Matrix.mulVec_zero]
    have hinj : ∀ a b : Fin 13 → ℂ, U *ᵥ a = U *ᵥ b → a = b := by
      intro a b hab
      have h1 := congrArg (fun z => V *ᵥ z) hab
      simp only at h1
      rwa [Matrix.mulVec_mulVec, V_mul_U, Matrix.one_mulVec, Matrix.mulVec_mulVec, V_mul_U,
        Matrix.one_mulVec] at h1
    have key : U *ᵥ (Matrix.diagonal eval13 *ᵥ w) = U *ᵥ (μ • w) := by
      rw [Matrix.mulVec_smul, hUw, Matrix.mulVec_mulVec, ← C13_mul_U, ← Matrix.mulVec_mulVec,
        hUw, hv]
    have key2 : Matrix.diagonal eval13 *ᵥ w = μ • w := hinj _ _ key
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hw0
    have hk' : eval13 k * w k = μ * w k := by
      have := congrFun key2 k
      simpa [Matrix.mulVec_diagonal] using this
    have hkμ : eval13 k = μ := mul_right_cancel₀ hk hk'
    exact ⟨(k : ℕ), k.isLt, by rw [← hkμ, eval13]⟩
  · rintro ⟨k, hk, rfl⟩
    refine ⟨vec ⟨k, hk⟩, vec_ne_zero _, ?_⟩
    rw [C13_mulVec_vec, eval13]

/-- The unit of the matrix ring given by the discrete Fourier matrix. -/
noncomputable def Uunit : (Matrix (Fin 13) (Fin 13) ℂ)ˣ :=
  ⟨U, V, U_mul_V, V_mul_U⟩

lemma C13_conj : C13 = (Uunit : Matrix (Fin 13) (Fin 13) ℂ) * Matrix.diagonal eval13 *
    ((Uunit⁻¹ : (Matrix (Fin 13) (Fin 13) ℂ)ˣ) : Matrix (Fin 13) (Fin 13) ℂ) :=
  calc C13 = C13 * (U * V) := by rw [U_mul_V, mul_one]
    _ = C13 * U * V := by rw [mul_assoc]
    _ = U * Matrix.diagonal eval13 * V := by rw [C13_mul_U]

/-- The characteristic polynomial of the Hückel matrix of `C₁₃` factors as
`∏ k, (X - 2 cos (2πk/13))`, so the thirteen eigenvalues (with multiplicity) are exactly
`2 cos (2πk/13)` for `k = 0, 1, …, 12`. -/
theorem huckel_C13_charpoly :
    C13.charpoly = ∏ k : Fin 13,
      (Polynomial.X - Polynomial.C ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 13) : ℝ) : ℂ)) := by
  rw [C13_conj, Matrix.charpoly_units_conj, Matrix.charpoly_diagonal]
  rfl

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

