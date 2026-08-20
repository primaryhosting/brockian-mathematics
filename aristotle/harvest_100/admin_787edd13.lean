/-
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The Hückel model for the cyclic polyene `C₁₅` has Hamiltonian `α + β A`, where `A` is the
adjacency matrix of the cycle graph `C₁₅`.  We show that the spectrum of `A` is exactly
`{2 cos (2πk/15) : k = 0, …, 14}`, by explicitly diagonalizing `A` with the discrete
Fourier matrix.
-/

namespace Chem

open Complex Matrix SimpleGraph Finset

/-- A primitive 15-th root of unity. -/
noncomputable def om : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 15)

lemma om_primitiveRoot : IsPrimitiveRoot om 15 :=
  Complex.isPrimitiveRoot_exp 15 (by norm_num)

lemma om_pow_15 : om ^ 15 = 1 := om_primitiveRoot.pow_eq_one

lemma om_ne_zero : om ≠ 0 := by
  intro h
  have := om_pow_15
  rw [h] at this
  norm_num at this

lemma om_pow_mod (a : ℕ) : om ^ (a % 15) = om ^ a := by
  conv_rhs => rw [← Nat.div_add_mod a 15, pow_add, pow_mul, om_pow_15, one_pow, one_mul]

lemma om_pow_mul_mod (a b : ℕ) : om ^ ((a % 15) * b) = om ^ (a * b) := by
  rw [← om_pow_mod ((a % 15) * b), ← om_pow_mod (a * b), Nat.mod_mul_mod]

lemma om_14 : om ^ 14 = om⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← pow_succ, om_pow_15]

/-- The Hückel (adjacency) eigenvalues of the 15-cycle. -/
noncomputable def lam (k : Fin 15) : ℂ := 2 * Real.cos (2 * Real.pi * (k.val : ℝ) / 15)

lemma om_pow_add_inv (k : Fin 15) : om ^ k.val + (om ^ k.val)⁻¹ = lam k := by
  have h1 : om ^ k.val = Complex.exp (((2 * Real.pi * (k.val : ℝ) / 15 : ℝ) : ℂ) * Complex.I) := by
    rw [om, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [h1, ← Complex.exp_neg, lam, Complex.ofReal_cos, Complex.two_cos]
  ring_nf

/-- The adjacency matrix of the cycle graph `C₁₅`. -/
noncomputable def A : Matrix (Fin 15) (Fin 15) ℂ := (SimpleGraph.cycleGraph 15).adjMatrix ℂ

/-- The discrete Fourier matrix on `Fin 15`. -/
noncomputable def P : Matrix (Fin 15) (Fin 15) ℂ := fun j k => om ^ (j.val * k.val)

/-- The inverse discrete Fourier matrix on `Fin 15`. -/
noncomputable def Q : Matrix (Fin 15) (Fin 15) ℂ :=
  fun k j => (15 : ℂ)⁻¹ * (om ^ (k.val * j.val))⁻¹

lemma key_sum (j j' : Fin 15) :
    ∑ k : Fin 15, om ^ (j.val * k.val) * (om ^ (k.val * j'.val))⁻¹
      = if j = j' then (15 : ℂ) else 0 := by
  set z : ℂ := om ^ j.val * (om ^ j'.val)⁻¹ with hz
  have hterm : ∀ k : Fin 15, om ^ (j.val * k.val) * (om ^ (k.val * j'.val))⁻¹ = z ^ k.val := by
    intro k
    rw [hz, mul_pow, ← pow_mul, inv_pow, ← pow_mul, mul_comm j'.val k.val]
  rw [Finset.sum_congr rfl (fun k _ => hterm k)]
  rw [Fin.sum_univ_eq_sum_range (fun i => z ^ i) 15]
  by_cases h : j = j'
  · subst h
    have hz1 : z = 1 := by
      rw [hz, ← div_eq_mul_inv]
      exact div_self (pow_ne_zero _ om_ne_zero)
    simp [hz1]
  · have hzne : z ≠ 1 := by
      rw [hz, ← div_eq_mul_inv]
      intro hc
      have hpow : om ^ j.val = om ^ j'.val :=
        (div_eq_one_iff_eq (pow_ne_zero _ om_ne_zero)).mp hc
      exact h (Fin.ext (om_primitiveRoot.pow_inj j.isLt j'.isLt hpow))
    have hz15 : z ^ 15 = 1 := by
      rw [hz, mul_pow, ← pow_mul, inv_pow, ← pow_mul, mul_comm j.val 15, mul_comm j'.val 15,
        pow_mul, pow_mul, om_pow_15, one_pow, one_pow]
      simp
    rw [geom_sum_eq hzne, hz15]
    simp [h]

lemma P_mul_Q : P * Q = 1 := by
  ext j j'
  rw [Matrix.mul_apply]
  have : ∀ k : Fin 15, P j k * Q k j'
      = (15 : ℂ)⁻¹ * (om ^ (j.val * k.val) * (om ^ (k.val * j'.val))⁻¹) := by
    intro k
    simp only [P, Q]
    ring
  rw [Finset.sum_congr rfl (fun k _ => this k), ← Finset.mul_sum, key_sum]
  by_cases h : j = j' <;> simp [h, Matrix.one_apply]

lemma Q_mul_P : Q * P = 1 := by
  ext k k'
  rw [Matrix.mul_apply]
  have : ∀ j : Fin 15, Q k j * P j k'
      = (15 : ℂ)⁻¹ * (om ^ (k'.val * j.val) * (om ^ (j.val * k.val))⁻¹) := by
    intro j
    simp only [P, Q, mul_comm k'.val j.val]
    ring
  rw [Finset.sum_congr rfl (fun j _ => this j), ← Finset.mul_sum, key_sum]
  by_cases h : k = k'
  · simp [h, Matrix.one_apply]
  · simp [h, Ne.symm h]

lemma P_succ (j k : Fin 15) : P (j + 1) k = P j k * om ^ k.val := by
  simp only [P]
  rw [Fin.add_def]
  simp only []
  rw [show ((1 : Fin 15).val) = 1 from rfl, om_pow_mul_mod, add_mul, pow_add, one_mul]

lemma P_pred (j k : Fin 15) : P (j - 1) k = P j k * (om ^ k.val)⁻¹ := by
  have h14 : om ^ (14 * k.val) = (om ^ k.val)⁻¹ := by
    rw [pow_mul, om_14, inv_pow]
  simp only [P]
  rw [Fin.sub_def]
  simp only []
  rw [show (15 - (1 : Fin 15).val) = 14 from rfl, om_pow_mul_mod, add_mul, pow_add, h14]
  ring

lemma A_mul_P : A * P = P * Matrix.diagonal lam := by
  ext j k
  have hne : (j - 1 : Fin 15) ≠ j + 1 := by revert j; decide
  have h : (A * P) j k = (A *ᵥ (fun m => P m k)) j := rfl
  have hnf : (SimpleGraph.cycleGraph 15).neighborFinset j = {j - 1, j + 1} :=
    SimpleGraph.cycleGraph_neighborFinset (n := 13)
  rw [h, A, SimpleGraph.adjMatrix_mulVec_apply, hnf, Finset.sum_pair hne, P_pred, P_succ,
    Matrix.mul_diagonal, ← om_pow_add_inv k]
  ring

lemma A_eq : A = P * Matrix.diagonal lam * Q := by
  rw [← A_mul_P, Matrix.mul_assoc, P_mul_Q, Matrix.mul_one]

theorem spectrum_A : spectrum ℂ A = Set.range lam := by
  have hdetPQ : P.det * Q.det = 1 := by
    rw [← Matrix.det_mul, P_mul_Q, Matrix.det_one]
  ext μ
  have hM : (algebraMap ℂ (Matrix (Fin 15) (Fin 15) ℂ)) μ - A
      = P * Matrix.diagonal (fun k => μ - lam k) * Q := by
    rw [← Matrix.diagonal_sub, Matrix.mul_sub, Matrix.sub_mul, ← A_eq]
    congr 1
    rw [← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, P_mul_Q,
      Matrix.algebraMap_eq_diagonal, Matrix.smul_one_eq_diagonal]
    rfl
  have hdet : ((algebraMap ℂ (Matrix (Fin 15) (Fin 15) ℂ)) μ - A).det = ∏ k, (μ - lam k) := by
    rw [hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
    calc P.det * (∏ k, (μ - lam k)) * Q.det
        = P.det * Q.det * ∏ k, (μ - lam k) := by ring
      _ = ∏ k, (μ - lam k) := by rw [hdetPQ, one_mul]
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, hdet, isUnit_iff_ne_zero, not_not,
    Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨k, -, hk⟩
    exact ⟨k, (sub_eq_zero.mp hk).symm⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, Finset.mem_univ k, sub_self _⟩

/-- The explicit Hückel eigenvectors: the discrete Fourier mode `j ↦ ω^(jk)` is an eigenvector
of the adjacency matrix of `C₁₅` with eigenvalue `2 cos (2πk/15)`. -/
theorem huckel_C15_eigenvector (k : Fin 15) :
    ((SimpleGraph.cycleGraph 15).adjMatrix ℂ) *ᵥ (fun j : Fin 15 => om ^ (j.val * k.val))
      = (2 * Real.cos (2 * Real.pi * (k.val : ℝ) / 15) : ℂ) •
          (fun j : Fin 15 => om ^ (j.val * k.val)) := by
  funext j
  have h : (A * P) j k = (P * Matrix.diagonal lam) j k := by rw [A_mul_P]
  rw [Matrix.mul_diagonal] at h
  simpa [A, P, lam, Pi.smul_apply, mul_comm] using h

theorem huckel_C15 :
    spectrum ℂ ((SimpleGraph.cycleGraph 15).adjMatrix ℂ)
      = {μ : ℂ | ∃ k : Fin 15, μ = 2 * Real.cos (2 * Real.pi * (k.val : ℝ) / 15)} := by
  have := spectrum_A
  rw [A] at this
  rw [this]
  ext μ
  simp [lam, eq_comm]

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

