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
-/

namespace Chem

open Matrix SimpleGraph Complex

/-- The primitive 18-th root of unity `exp(2πi/18)`. -/
noncomputable def om : ℂ := Complex.exp (2 * Real.pi * Complex.I / 18)

lemma om_primitive : IsPrimitiveRoot om 18 := by
  simpa [om] using Complex.isPrimitiveRoot_exp 18 (by norm_num)

lemma om_pow_18 : om ^ 18 = 1 := om_primitive.pow_eq_one

lemma om_pow_congr {a b : ℕ} (h : a % 18 = b % 18) : om ^ a = om ^ b := by
  conv_lhs => rw [← Nat.div_add_mod a 18]
  conv_rhs => rw [← Nat.div_add_mod b 18]
  rw [pow_add, pow_add, pow_mul, pow_mul, om_pow_18, one_pow, one_pow, h]

lemma om_pow_injOn {i j : ℕ} (hi : i < 18) (hj : j < 18) (h : om ^ i = om ^ j) : i = j :=
  om_primitive.pow_inj hi hj h

/-- The DFT / Vandermonde matrix built from powers of `om`. -/
noncomputable def V : Matrix (Fin 18) (Fin 18) ℂ :=
  Matrix.vandermonde (fun j : Fin 18 => om ^ (j : ℕ))

lemma V_apply (j k : Fin 18) : V j k = om ^ ((j : ℕ) * (k : ℕ)) := by
  simp [V, Matrix.vandermonde, pow_mul]

/-- The diagonal matrix of Hückel eigenvalues of `C₁₈`. -/
noncomputable def D : Matrix (Fin 18) (Fin 18) ℂ :=
  Matrix.diagonal (fun k : Fin 18 => (2 * Real.cos (2 * Real.pi * (k : ℕ) / 18) : ℂ))

lemma V_isUnit : IsUnit V := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  rw [V, Ne, Matrix.det_vandermonde_eq_zero_iff]
  rintro ⟨i, j, hij, hne⟩
  exact hne (Fin.ext (om_pow_injOn i.isLt j.isLt hij))

lemma om_pow_add_inv (k : Fin 18) :
    om ^ (k : ℕ) + om ^ (17 * (k : ℕ)) = (2 * Real.cos (2 * Real.pi * (k : ℕ) / 18) : ℂ) := by
  have hz : om ^ (k : ℕ) = Complex.exp ((2 * Real.pi * (k : ℕ) / 18 : ℝ) * Complex.I) := by
    rw [om, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hz' : om ^ (17 * (k : ℕ)) = Complex.exp (-(2 * Real.pi * (k : ℕ) / 18 : ℝ) * Complex.I) := by
    have h1 : om ^ (17 * (k : ℕ)) * om ^ (k : ℕ) = 1 := by
      rw [← pow_add]
      have h18 : 17 * (k : ℕ) + (k : ℕ) = 18 * (k : ℕ) := by ring
      rw [h18, pow_mul, om_pow_18, one_pow]
    have hne : om ^ (k : ℕ) ≠ 0 := pow_ne_zero _ (by
      simp [om, Complex.exp_ne_zero])
    have h2 := eq_div_of_mul_eq hne h1
    rw [h2, hz, one_div, ← Complex.exp_neg]
    congr 1
    push_cast
    ring
  rw [hz, hz', Complex.ofReal_cos, Complex.cos]
  push_cast
  ring_nf

lemma adj_mul_V : (cycleGraph 18).adjMatrix ℂ * V = V * D := by
  ext j k
  rw [SimpleGraph.adjMatrix_mul_apply, D, Matrix.mul_diagonal]
  have hnb : (cycleGraph 18).neighborFinset j = {j - 1, j + 1} :=
    cycleGraph_neighborFinset (n := 16) (v := j)
  have hne : j - 1 ≠ j + 1 := by
    intro h
    rw [sub_eq_add_neg] at h
    exact absurd (add_left_cancel h) (by decide)
  rw [hnb, Finset.sum_pair hne]
  have h1 : j - 1 = j + 17 := by
    rw [sub_eq_add_neg]
    congr 1
  rw [h1, V_apply, V_apply, V_apply]
  have e1 : ((j + 17 : Fin 18) : ℕ) * (k : ℕ) % 18 = ((j : ℕ) + 17) * (k : ℕ) % 18 := by
    rw [Fin.val_add]
    simp [Nat.mul_mod, Nat.add_mod]
  have e2 : ((j + 1 : Fin 18) : ℕ) * (k : ℕ) % 18 = ((j : ℕ) + 1) * (k : ℕ) % 18 := by
    rw [Fin.val_add]
    simp [Nat.mul_mod, Nat.add_mod]
  rw [om_pow_congr e1, om_pow_congr e2]
  have expand1 : ((j : ℕ) + 17) * (k : ℕ) = (j : ℕ) * (k : ℕ) + 17 * (k : ℕ) := by ring
  have expand2 : ((j : ℕ) + 1) * (k : ℕ) = (j : ℕ) * (k : ℕ) + (k : ℕ) := by ring
  rw [expand1, expand2, pow_add, pow_add, ← om_pow_add_inv k]
  ring

/-- **Hückel theory for the C₁₈ annulene.**
The eigenvalues of the adjacency matrix of the cycle graph `C₁₈` are exactly the
numbers `2 cos(2πk/18)` for `k = 0, …, 17`. -/
theorem huckel_C18 (μ : ℂ) :
    (∃ w : Fin 18 → ℂ, w ≠ 0 ∧ (cycleGraph 18).adjMatrix ℂ *ᵥ w = μ • w) ↔
      ∃ k : Fin 18, μ = 2 * Real.cos (2 * Real.pi * (k : ℕ) / 18) := by
  constructor
  · rintro ⟨w, hw, hev⟩
    obtain ⟨u, hu⟩ : ∃ u, V *ᵥ u = w := by
      have hdet : IsUnit V.det := (Matrix.isUnit_iff_isUnit_det V).mp V_isUnit
      refine ⟨V⁻¹ *ᵥ w, ?_⟩
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv V hdet, Matrix.one_mulVec]
    have hDu : V *ᵥ (D *ᵥ u) = V *ᵥ (μ • u) := by
      rw [Matrix.mulVec_mulVec, ← adj_mul_V, ← Matrix.mulVec_mulVec, hu, hev,
        Matrix.mulVec_smul, hu]
    have h2 : D *ᵥ u = μ • u := Matrix.mulVec_injective_of_isUnit V_isUnit hDu
    have hune : u ≠ 0 := by
      rintro rfl
      exact hw (by rw [← hu]; simp)
    obtain ⟨k, hk⟩ : ∃ k, u k ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hune (funext hc)
    refine ⟨k, ?_⟩
    have := congrFun h2 k
    rw [D, Matrix.mulVec_diagonal] at this
    simp only [Pi.smul_apply, smul_eq_mul] at this
    exact (mul_right_cancel₀ hk this).symm
  · rintro ⟨k, rfl⟩
    refine ⟨fun j => V j k, ?_, ?_⟩
    · intro h
      have := congrFun h 0
      rw [V_apply] at this
      simp only [Pi.zero_apply] at this
      exact absurd this (pow_ne_zero _ (by simp [om, Complex.exp_ne_zero]))
    · funext j
      have h := congrFun (congrFun adj_mul_V j) k
      rw [Matrix.mul_apply, D, Matrix.mul_diagonal] at h
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
      rw [h]
      ring

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

