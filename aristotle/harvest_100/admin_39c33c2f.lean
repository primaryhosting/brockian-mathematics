/-
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
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

open Matrix Polynomial

/-- The adjacency matrix (Hückel matrix, with `α = 0`, `β = 1`) of the cycle graph `C₁₀`. -/
noncomputable def C10adj : Matrix (Fin 10) (Fin 10) ℂ :=
  (SimpleGraph.cycleGraph 10).adjMatrix ℂ

/-- The `k`-th Hückel eigenvalue of `C₁₀`: `2 cos (2πk/10)`. -/
noncomputable def huckelEigenvalue (k : Fin 10) : ℝ :=
  2 * Real.cos (2 * Real.pi * (k : ℕ) / 10)

/-- A primitive 10-th root of unity. -/
noncomputable def w : ℂ := Complex.exp (2 * Real.pi * Complex.I / 10)

/-- The (unnormalised) discrete Fourier transform matrix. -/
noncomputable def dftP : Matrix (Fin 10) (Fin 10) ℂ :=
  Matrix.of fun j k => w ^ ((j : ℕ) * (k : ℕ))

/-- The inverse of `dftP`. -/
noncomputable def dftQ : Matrix (Fin 10) (Fin 10) ℂ :=
  Matrix.of fun k l => (10 : ℂ)⁻¹ * w ^ ((k : ℕ) * (10 - (l : ℕ)))

lemma w_primitive : IsPrimitiveRoot w 10 := by
  have h := Complex.isPrimitiveRoot_exp 10 (by norm_num)
  unfold w
  convert h using 3

lemma w_pow_ten : w ^ 10 = 1 := w_primitive.pow_eq_one

lemma w_pow_mul_ten (a : ℕ) : (w ^ a) ^ 10 = 1 := by
  rw [← pow_mul, Nat.mul_comm, pow_mul, w_pow_ten, one_pow]

lemma w_pow_eq_one_iff (a : ℕ) : w ^ a = 1 ↔ 10 ∣ a :=
  w_primitive.pow_eq_one_iff_dvd a

lemma geom_sum_w (a : ℕ) :
    ∑ k : Fin 10, w ^ ((k : ℕ) * a) = if 10 ∣ a then (10 : ℂ) else 0 := by
  have hz : ∀ k : Fin 10, w ^ ((k : ℕ) * a) = (w ^ a) ^ (k : ℕ) := fun k => by
    rw [← pow_mul, Nat.mul_comm]
  simp only [hz]
  rw [Fin.sum_univ_eq_sum_range (fun i => (w ^ a) ^ i) 10]
  by_cases h : 10 ∣ a
  · have hone : w ^ a = 1 := (w_pow_eq_one_iff a).mpr h
    simp [hone, h]
  · have hne : w ^ a ≠ 1 := fun hc => h ((w_pow_eq_one_iff a).mp hc)
    rw [geom_sum_eq hne, w_pow_mul_ten]
    simp [h]

lemma dftP_mul_dftQ : dftP * dftQ = 1 := by
  ext j l
  rw [Matrix.mul_apply]
  simp only [dftP, dftQ, Matrix.of_apply]
  have hterm : ∀ k : Fin 10,
      w ^ ((j : ℕ) * (k : ℕ)) * ((10 : ℂ)⁻¹ * w ^ ((k : ℕ) * (10 - (l : ℕ))))
        = (10 : ℂ)⁻¹ * w ^ ((k : ℕ) * ((j : ℕ) + (10 - (l : ℕ)))) := by
    intro k
    rw [Nat.mul_add, pow_add, Nat.mul_comm (j : ℕ) (k : ℕ)]
    ring
  simp only [hterm]
  rw [← Finset.mul_sum, geom_sum_w]
  have hj := j.isLt
  have hl := l.isLt
  have hiff : (10 ∣ (j : ℕ) + (10 - (l : ℕ))) ↔ j = l := by
    rw [Fin.ext_iff]
    omega
  rw [Matrix.one_apply]
  by_cases h : j = l
  · rw [if_pos (hiff.mpr h), if_pos h]
    norm_num
  · rw [if_neg (fun hc => h (hiff.mp hc)), if_neg h]
    ring

lemma dftQ_mul_dftP : dftQ * dftP = 1 := mul_eq_one_comm.mp dftP_mul_dftQ

/-- The diagonal matrix of eigenvalues. -/
noncomputable def eigDiag : Matrix (Fin 10) (Fin 10) ℂ :=
  Matrix.diagonal fun k => ((huckelEigenvalue k : ℝ) : ℂ)

lemma huckelEigenvalue_eq (k : Fin 10) :
    ((huckelEigenvalue k : ℝ) : ℂ) = w ^ (k : ℕ) + (w ^ (k : ℕ)) ^ 9 := by
  set t : ℝ := 2 * Real.pi * (k : ℕ) / 10 with ht
  have hw : w ^ (k : ℕ) = Complex.exp ((t : ℂ) * Complex.I) := by
    rw [w, ← Complex.exp_nat_mul]
    congr 1
    rw [ht]
    push_cast
    ring
  have h1 : Complex.exp ((t : ℂ) * Complex.I) * Complex.exp (-(t : ℂ) * Complex.I) = 1 := by
    rw [← Complex.exp_add]
    ring_nf
    simp
  have hinv : (w ^ (k : ℕ)) ^ 9 = Complex.exp (-(t : ℂ) * Complex.I) := by
    have h2 : (w ^ (k : ℕ)) ^ 9 * Complex.exp ((t : ℂ) * Complex.I) = 1 := by
      rw [← hw, ← pow_succ]
      exact w_pow_mul_ten (k : ℕ)
    have hne : Complex.exp ((t : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
    apply mul_right_cancel₀ hne
    rw [h2, mul_comm, h1]
  rw [hinv, hw, huckelEigenvalue, ← ht]
  push_cast [Complex.ofReal_cos]
  rw [Complex.two_cos]

lemma C10adj_mul_dftP : C10adj * dftP = dftP * eigDiag := by
  ext j k
  have hP : ∀ i : Fin 10, dftP i k = (w ^ (k : ℕ)) ^ (i : ℕ) := by
    intro i
    simp only [dftP, Matrix.of_apply]
    rw [← pow_mul, Nat.mul_comm]
  have hz : (w ^ (k : ℕ)) ^ 10 = 1 := w_pow_mul_ten (k : ℕ)
  rw [Matrix.mul_apply, eigDiag, Matrix.mul_diagonal, hP, huckelEigenvalue_eq]
  simp only [hP]
  set z : ℂ := w ^ (k : ℕ) with hzdef
  clear_value z
  clear hP hzdef
  fin_cases j <;>
    simp +decide [C10adj, SimpleGraph.adjMatrix_apply, Fin.sum_univ_succ]
  · linear_combination -hz
  · linear_combination -z * hz
  · linear_combination -z ^ 2 * hz
  · linear_combination -z ^ 3 * hz
  · linear_combination -z ^ 4 * hz
  · linear_combination -z ^ 5 * hz
  · linear_combination -z ^ 6 * hz
  · linear_combination -z ^ 7 * hz
  · linear_combination -(1 + z ^ 8) * hz

/-- The unit of the matrix algebra given by the DFT matrix. -/
noncomputable def dftUnit : (Matrix (Fin 10) (Fin 10) ℂ)ˣ :=
  ⟨dftP, dftQ, dftP_mul_dftQ, dftQ_mul_dftP⟩

lemma C10adj_conj : C10adj = dftP * eigDiag * dftQ := by
  calc C10adj = C10adj * (dftP * dftQ) := by rw [dftP_mul_dftQ, Matrix.mul_one]
  _ = (C10adj * dftP) * dftQ := by rw [Matrix.mul_assoc]
  _ = dftP * eigDiag * dftQ := by rw [C10adj_mul_dftP]

/-- **Hückel theory for `C₁₀`.**  The characteristic polynomial of the adjacency matrix of
the cycle graph `C₁₀` is `∏_{k=0}^{9} (X - 2 cos (2πk/10))`, and consequently its spectrum
(the set of Hückel eigenvalues) is exactly `{2 cos (2πk/10) : k = 0, …, 9}`. -/
theorem huckel_C10 :
    C10adj.charpoly = ∏ k : Fin 10, (X - C ((huckelEigenvalue k : ℝ) : ℂ)) ∧
      spectrum ℂ C10adj = Set.range fun k : Fin 10 => ((huckelEigenvalue k : ℝ) : ℂ) := by
  have hu : (dftUnit : Matrix (Fin 10) (Fin 10) ℂ) = dftP := rfl
  have hui : ((dftUnit⁻¹ : (Matrix (Fin 10) (Fin 10) ℂ)ˣ) : Matrix (Fin 10) (Fin 10) ℂ) = dftQ :=
    rfl
  constructor
  · rw [C10adj_conj, ← hu, ← hui, Matrix.charpoly_units_conj]
    rw [eigDiag, Matrix.charpoly_diagonal]
  · rw [C10adj_conj]
    have hconj : dftP * eigDiag * dftQ
        = (dftUnit : Matrix (Fin 10) (Fin 10) ℂ) * eigDiag *
            (dftUnit⁻¹ : (Matrix (Fin 10) (Fin 10) ℂ)ˣ) := by
      rw [hu, hui]
    rw [hconj, spectrum.units_conjugate, eigDiag, _root_.spectrum_diagonal]

end Chem

