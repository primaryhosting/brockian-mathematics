/-
# Von Neumann Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.vonNeumann_trace_ineq
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

namespace Zeta23Redux.LinAlg

open Matrix Finset

section Core

variable {d : ℕ}

/-- Two antitone real sequences monovary. -/
lemma monovary_of_antitone {mu nu : Fin d → ℝ} (hmu : Antitone mu) (hnu : Antitone nu) :
    Monovary mu nu := by
  intro i j hij
  rcases le_total i j with h | h
  · exact absurd (hnu h) (not_le.2 hij)
  · exact hmu h

/-- The bilinear form of two antitone sequences against a doubly stochastic matrix is
maximised by the diagonal (identity) pairing.  This combines Birkhoff's theorem
(`exists_eq_sum_perm_of_mem_doublyStochastic`) with the rearrangement inequality
(`Monovary.sum_mul_comp_perm_le_sum_mul`). -/
lemma sum_mul_doublyStochastic_le {mu nu : Fin d → ℝ} (hmu : Antitone mu) (hnu : Antitone nu)
    {S : Matrix (Fin d) (Fin d) ℝ} (hS : S ∈ doublyStochastic ℝ (Fin d)) :
    ∑ i, ∑ j, mu i * nu j * S i j ≤ ∑ i, mu i * nu i := by
  obtain ⟨w, hw0, hw1, hwS⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hS
  have hentry : ∀ i j, S i j = ∑ σ : Equiv.Perm (Fin d), w σ * (σ.permMatrix ℝ i j) := by
    intro i j
    rw [← hwS]
    simp [Matrix.sum_apply, smul_eq_mul]
  have hperm : ∀ σ : Equiv.Perm (Fin d),
      ∑ i, ∑ j, mu i * nu j * (σ.permMatrix ℝ i j) = ∑ i, mu i * nu (σ i) := by
    intro σ
    refine Finset.sum_congr rfl fun i _ => ?_
    have h : ∀ j : Fin d, mu i * nu j * (σ.permMatrix ℝ i j)
        = if j = σ i then mu i * nu j else 0 := by
      intro j
      by_cases hj : j = σ i
      · subst hj; simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
      · simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
          Ne.symm hj, hj]
    rw [Finset.sum_congr rfl fun j _ => h j, Finset.sum_ite_eq' Finset.univ (σ i)]
    simp
  calc ∑ i, ∑ j, mu i * nu j * S i j
      = ∑ i, ∑ j, ∑ σ : Equiv.Perm (Fin d), w σ * (mu i * nu j * (σ.permMatrix ℝ i j)) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [hentry i j, Finset.mul_sum]
        exact Finset.sum_congr rfl fun σ _ => by ring
    _ = ∑ i, ∑ σ : Equiv.Perm (Fin d), ∑ j, w σ * (mu i * nu j * (σ.permMatrix ℝ i j)) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ σ : Equiv.Perm (Fin d), ∑ i, ∑ j, w σ * (mu i * nu j * (σ.permMatrix ℝ i j)) :=
        Finset.sum_comm
    _ = ∑ σ : Equiv.Perm (Fin d), w σ * ∑ i, ∑ j, mu i * nu j * (σ.permMatrix ℝ i j) := by
        simp [Finset.mul_sum]
    _ = ∑ σ : Equiv.Perm (Fin d), w σ * ∑ i, mu i * nu (σ i) :=
        Finset.sum_congr rfl fun σ _ => by rw [hperm σ]
    _ ≤ ∑ σ : Equiv.Perm (Fin d), w σ * ∑ i, mu i * nu i := by
        refine Finset.sum_le_sum fun σ _ => ?_
        exact mul_le_mul_of_nonneg_left
          ((monovary_of_antitone hmu hnu).sum_mul_comp_perm_le_sum_mul) (hw0 σ)
    _ = ∑ i, mu i * nu i := by rw [← Finset.sum_mul, hw1, one_mul]

end Core

section Spectral

variable {d : ℕ}

/-- Spectral theorem for Hermitian matrices, with the eigenvalues listed in an arbitrary
(permuted) order. -/
lemma exists_unitary_conj_diagonal {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian)
    (mu : Fin d → ℝ) (σ : Equiv.Perm (Fin d)) (hmu : ∀ i, mu i = hA.eigenvalues (σ i)) :
    ∃ U : Matrix (Fin d) (Fin d) ℂ, Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      A = U * diagonal (fun i => (mu i : ℂ)) * Uᴴ := by
  set W0 : Matrix (Fin d) (Fin d) ℂ := (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) with hW0
  have hu := hA.eigenvectorUnitary.2
  have h1 : W0ᴴ * W0 = 1 := hu.1
  have h2 : W0 * W0ᴴ = 1 := hu.2
  have hspec : A = W0 * diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) * W0ᴴ := by
    have h := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    simpa [mul_assoc, Function.comp_def] using h
  refine ⟨W0.submatrix id σ, ?_, ?_, ?_⟩
  · ext i j
    have hij : (W0ᴴ * W0) (σ i) (σ j) = (1 : Matrix (Fin d) (Fin d) ℂ) (σ i) (σ j) := by rw [h1]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply, id] at *
    rw [hij]
    simp [Matrix.one_apply, σ.injective.eq_iff]
  · ext i j
    have hij : (W0 * W0ᴴ) i j = (1 : Matrix (Fin d) (Fin d) ℂ) i j := by rw [h2]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply, id] at *
    rw [← hij]
    exact Equiv.sum_comp σ (fun k => W0 i k * star (W0 j k))
  · ext i k
    have h := congrFun (congrFun hspec i) k
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply, id,
      Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true] at *
    rw [h]
    simp only [hmu]
    exact (Equiv.sum_comp σ (fun j => W0 i j * ((hA.eigenvalues j : ℝ) : ℂ) * star (W0 k j))).symm

/-- The entrywise squared modulus of a unitary matrix is doubly stochastic. -/
lemma normSq_mem_doublyStochastic {W : Matrix (Fin d) (Fin d) ℂ}
    (h1 : Wᴴ * W = 1) (h2 : W * Wᴴ = 1) :
    (Matrix.of fun i j => Complex.normSq (W i j)) ∈ doublyStochastic ℝ (Fin d) := by
  have key : ∀ z : ℂ, z * star z = (Complex.normSq z : ℂ) := fun z => Complex.mul_conj z
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨fun i j => Complex.normSq_nonneg _, fun i => ?_, fun j => ?_⟩
  · have h := congrFun (congrFun h2 i) i
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at h
    have hc : ((∑ j, Complex.normSq (W i j) : ℝ) : ℂ) = (1 : ℂ) := by
      push_cast; rw [← h]; exact Finset.sum_congr rfl fun x _ => (key _).symm
    exact_mod_cast hc
  · have h := congrFun (congrFun h1 j) j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at h
    have hc : ((∑ i, Complex.normSq (W i j) : ℝ) : ℂ) = (1 : ℂ) := by
      push_cast; rw [← h]
      exact Finset.sum_congr rfl fun x _ => by rw [mul_comm]; exact (key _).symm
    exact_mod_cast hc

end Spectral

/-- **Von Neumann's trace inequality** for Hermitian complex matrices.

If `A` and `B` are Hermitian matrices of size `d`, and `mu`, `nu` list the eigenvalues of `A`
and `B` respectively (i.e. each is a permutation of the eigenvalue list), both arranged in
decreasing (antitone) order, then `Re (trace (A * B)) ≤ ∑ i, mu i * nu i`.

The proof diagonalises both matrices, reduces the trace to a bilinear form against the
doubly stochastic matrix of entrywise squared moduli of a unitary, and then applies
Birkhoff's theorem together with the rearrangement inequality. -/
theorem vonNeumann_trace_ineq {d : ℕ} {A B : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) {mu nu : Fin d → ℝ}
    (hmu : Antitone mu) (hnu : Antitone nu)
    (hmuA : ∃ σ : Equiv.Perm (Fin d), ∀ i, mu i = hA.eigenvalues (σ i))
    (hnuB : ∃ τ : Equiv.Perm (Fin d), ∀ i, nu i = hB.eigenvalues (τ i)) :
    (Matrix.trace (A * B)).re ≤ ∑ i, mu i * nu i := by
  obtain ⟨σ, hσ⟩ := hmuA
  obtain ⟨τ, hτ⟩ := hnuB
  obtain ⟨U, hU1, hU2, hUA⟩ := exists_unitary_conj_diagonal hA mu σ hσ
  obtain ⟨V, hV1, hV2, hVB⟩ := exists_unitary_conj_diagonal hB nu τ hτ
  set Dmu : Matrix (Fin d) (Fin d) ℂ := diagonal (fun i => (mu i : ℂ)) with hDmu
  set Dnu : Matrix (Fin d) (Fin d) ℂ := diagonal (fun i => (nu i : ℂ)) with hDnu
  set W : Matrix (Fin d) (Fin d) ℂ := Uᴴ * V with hW
  have hWH : Wᴴ = Vᴴ * U := by
    rw [hW, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hW1 : Wᴴ * W = 1 := by
    rw [hWH, hW]
    calc Vᴴ * U * (Uᴴ * V) = Vᴴ * (U * Uᴴ) * V := by simp [Matrix.mul_assoc]
      _ = 1 := by rw [hU2, Matrix.mul_one, hV1]
  have hW2 : W * Wᴴ = 1 := by
    rw [hWH, hW]
    calc Uᴴ * V * (Vᴴ * U) = Uᴴ * (V * Vᴴ) * U := by simp [Matrix.mul_assoc]
      _ = 1 := by rw [hV2, Matrix.mul_one, hU1]
  have hAB : A * B = U * (Dmu * W * Dnu * Wᴴ) * Uᴴ := by
    rw [hWH, hW, hUA, hVB]
    simp [Matrix.mul_assoc, hU2]
  have htr : Matrix.trace (A * B) = Matrix.trace (Dmu * W * Dnu * Wᴴ) := by
    rw [hAB, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU1, Matrix.one_mul]
  have key : ∀ z : ℂ, z * star z = (Complex.normSq z : ℂ) := fun z => Complex.mul_conj z
  have hentry : ∀ i, (Dmu * W * Dnu * Wᴴ) i i
      = ((∑ j, mu i * nu j * Complex.normSq (W i j) : ℝ) : ℂ) := by
    intro i
    rw [Matrix.mul_apply]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mul_diagonal, hDmu, Matrix.diagonal_mul, Matrix.conjTranspose_apply]
    linear_combination ((mu i : ℂ) * (nu j : ℂ)) * key (W i j)
  have hsum : Matrix.trace (A * B)
      = ((∑ i, ∑ j, mu i * nu j * Complex.normSq (W i j) : ℝ) : ℂ) := by
    rw [htr, Matrix.trace]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.diag_apply, hentry i]
    push_cast
    ring
  rw [hsum, Complex.ofReal_re]
  exact sum_mul_doublyStochastic_le hmu hnu (normSq_mem_doublyStochastic hW1 hW2)

end Zeta23Redux.LinAlg

