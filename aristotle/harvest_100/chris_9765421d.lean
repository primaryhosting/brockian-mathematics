/-
# Von Neumann Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.vonNeumann_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Von Neumann Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.vonNeumann_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Matrix

namespace Zeta23Redux.LinAlg

/-- **Rearrangement against a doubly stochastic matrix.** If `S` is doubly stochastic and
`mu`, `nu` are both antitone, then the bilinear form `∑ i j, mu i * S i j * nu j` is at most
the aligned sum `∑ i, mu i * nu i`.  Proved via Birkhoff's theorem plus the rearrangement
inequality. -/
theorem sum_mul_doublyStochastic_le {d : ℕ} {S : Matrix (Fin d) (Fin d) ℝ}
    (hS : S ∈ doublyStochastic ℝ (Fin d)) {mu nu : Fin d → ℝ}
    (hmu : Antitone mu) (hnu : Antitone nu) :
    ∑ i, ∑ j, mu i * S i j * nu j ≤ ∑ i, mu i * nu i := by
  have hmn : Monovary mu nu := by
    intro i j hij
    have : j < i := by
      by_contra h
      exact absurd (hnu (not_lt.mp h)) (not_le.mpr hij)
    exact hmu this.le
  obtain ⟨w, hw0, hw1, hwS⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hS
  have key : ∀ σ : Equiv.Perm (Fin d),
      ∑ i, ∑ j, mu i * (σ.permMatrix ℝ) i j * nu j ≤ ∑ i, mu i * nu i := by
    intro σ
    have hrow : ∀ i, ∑ j, mu i * (σ.permMatrix ℝ) i j * nu j = mu i * nu (σ i) := by
      intro i
      simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
    rw [Finset.sum_congr rfl fun i _ => hrow i]
    simpa using hmn.sum_smul_comp_perm_le_sum_smul (σ := σ)
  calc ∑ i, ∑ j, mu i * S i j * nu j
      = ∑ σ : Equiv.Perm (Fin d), w σ * ∑ i, ∑ j, mu i * (σ.permMatrix ℝ) i j * nu j := by
        rw [← hwS]
        simp only [Matrix.sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
            Finset.sum_comm (s := (Finset.univ : Finset (Fin d)))
              (t := (Finset.univ : Finset (Equiv.Perm (Fin d))))
              (f := fun j σ => mu i * (w σ * (σ.permMatrix ℝ) i j) * nu j),
          Finset.sum_comm]
        exact Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun i _ =>
          Finset.sum_congr rfl fun j _ => by ring
    _ ≤ ∑ σ : Equiv.Perm (Fin d), w σ * ∑ i, mu i * nu i :=
        Finset.sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left (key σ) (hw0 σ)
    _ = ∑ i, mu i * nu i := by rw [← Finset.sum_mul, hw1, one_mul]

/-- The trace of `diagonal a * W * diagonal b * Wᴴ` is the real number
`∑ i j, a i * b j * ‖W i j‖ ^ 2`. -/
theorem trace_diagonal_mul_conjTranspose {d : ℕ} (a b : Fin d → ℝ)
    (W : Matrix (Fin d) (Fin d) ℂ) :
    Matrix.trace (diagonal (fun i => (a i : ℂ)) * W * diagonal (fun i => (b i : ℂ)) * Wᴴ)
      = ((∑ i, ∑ j, a i * b j * Complex.normSq (W i j) : ℝ) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.diagonal_apply,
    Matrix.conjTranspose_apply, Complex.ofReal_sum, Complex.ofReal_mul]
  simp only [ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_ite_eq]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h := Complex.mul_conj (W i j)
  simp only [starRingEnd_apply] at h
  linear_combination ((a i : ℂ) * (b j : ℂ)) * h

/-- For a unitary matrix `W`, the entrywise squared moduli form a doubly stochastic matrix. -/
theorem normSq_mem_doublyStochastic {d : ℕ} {W : Matrix (Fin d) (Fin d) ℂ}
    (hW : W * Wᴴ = 1) (hW' : Wᴴ * W = 1) :
    (Matrix.of fun i j => Complex.normSq (W i j)) ∈ doublyStochastic ℝ (Fin d) := by
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨fun i j => Complex.normSq_nonneg _, fun i => ?_, fun j => ?_⟩
  · have h := congrArg (fun M => M i i) hW
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at h
    have : ((∑ j, Complex.normSq (W i j) : ℝ) : ℂ) = 1 := by
      rw [Complex.ofReal_sum]
      rw [← h]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hc := Complex.mul_conj (W i j)
      simp only [starRingEnd_apply] at hc
      exact hc.symm
    exact_mod_cast this
  · have h := congrArg (fun M => M j j) hW'
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at h
    have : ((∑ i, Complex.normSq (W i j) : ℝ) : ℂ) = 1 := by
      rw [Complex.ofReal_sum]
      rw [← h]
      refine Finset.sum_congr rfl fun i _ => ?_
      have := Complex.mul_conj (W i j)
      simp only [starRingEnd_apply] at this
      rw [← this]; ring
    exact_mod_cast this

/-- Core step: if `A` and `B` are unitarily diagonalised with real spectra `a` and `b`, then
`Re (trace (A * B))` is a doubly stochastic bilinear form in `a` and `b`. -/
theorem exists_doublyStochastic_trace_eq {d : ℕ} {A B U V : Matrix (Fin d) (Fin d) ℂ}
    {a b : Fin d → ℝ}
    (hU : U * Uᴴ = 1) (hU' : Uᴴ * U = 1) (hV : V * Vᴴ = 1) (hV' : Vᴴ * V = 1)
    (hA : A = U * diagonal (fun i => (a i : ℂ)) * Uᴴ)
    (hB : B = V * diagonal (fun i => (b i : ℂ)) * Vᴴ) :
    ∃ S : Matrix (Fin d) (Fin d) ℝ, S ∈ doublyStochastic ℝ (Fin d) ∧
      (Matrix.trace (A * B)).re = ∑ i, ∑ j, a i * S i j * b j := by
  set W : Matrix (Fin d) (Fin d) ℂ := Uᴴ * V with hWdef
  have hWH : Wᴴ = Vᴴ * U := by
    simp [hWdef, Matrix.conjTranspose_mul]
  have hWW : W * Wᴴ = 1 := by
    rw [hWdef, hWH]
    calc Uᴴ * V * (Vᴴ * U) = Uᴴ * (V * Vᴴ) * U := by simp [Matrix.mul_assoc]
      _ = 1 := by rw [hV]; simp [hU']
  have hWW' : Wᴴ * W = 1 := by
    rw [hWdef, hWH]
    calc Vᴴ * U * (Uᴴ * V) = Vᴴ * (U * Uᴴ) * V := by simp [Matrix.mul_assoc]
      _ = 1 := by rw [hU]; simp [hV']
  refine ⟨Matrix.of fun i j => Complex.normSq (W i j),
    normSq_mem_doublyStochastic hWW hWW', ?_⟩
  have htr : Matrix.trace (A * B)
      = ((∑ i, ∑ j, a i * b j * Complex.normSq (W i j) : ℝ) : ℂ) := by
    rw [← trace_diagonal_mul_conjTranspose a b W]
    rw [hA, hB]
    rw [show U * diagonal (fun i => (a i : ℂ)) * Uᴴ * (V * diagonal (fun i => (b i : ℂ)) * Vᴴ)
        = U * (diagonal (fun i => (a i : ℂ)) * Uᴴ * V * diagonal (fun i => (b i : ℂ)) * Vᴴ) by
      simp [Matrix.mul_assoc]]
    rw [Matrix.trace_mul_comm]
    congr 1
    rw [hWH, hWdef]
    simp [Matrix.mul_assoc]
  rw [htr, Complex.ofReal_re]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    simp only [Matrix.of_apply]; ring

/-- **Von Neumann's trace inequality** for Hermitian complex matrices.
If `A` and `B` are Hermitian `d × d` complex matrices and `mu`, `nu` list the eigenvalues of
`A` and `B` respectively (as rearrangements `sA`, `sB` of `Matrix.IsHermitian.eigenvalues`),
both in decreasing order, then `Re (trace (A * B)) ≤ ∑ i, mu i * nu i`. -/
theorem vonNeumann_trace_ineq {d : ℕ} {A B : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (mu nu : Fin d → ℝ)
    (sA sB : Equiv.Perm (Fin d))
    (hmu : mu = hA.eigenvalues ∘ sA) (hnu : nu = hB.eigenvalues ∘ sB)
    (hmu' : Antitone mu) (hnu' : Antitone nu) :
    (Matrix.trace (A * B)).re ≤ ∑ i, mu i * nu i := by
  classical
  set U : Matrix (Fin d) (Fin d) ℂ := (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) with hUdef
  set V : Matrix (Fin d) (Fin d) ℂ := (hB.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) with hVdef
  have hU' : Uᴴ * U = 1 := by
    rw [hUdef, ← Matrix.star_eq_conjTranspose]
    exact Unitary.coe_star_mul_self _
  have hU : U * Uᴴ = 1 := by
    rw [hUdef, ← Matrix.star_eq_conjTranspose]
    exact Unitary.coe_mul_star_self _
  have hV' : Vᴴ * V = 1 := by
    rw [hVdef, ← Matrix.star_eq_conjTranspose]
    exact Unitary.coe_star_mul_self _
  have hV : V * Vᴴ = 1 := by
    rw [hVdef, ← Matrix.star_eq_conjTranspose]
    exact Unitary.coe_mul_star_self _
  have hAeq : A = U * diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) * Uᴴ := by
    conv_lhs => rw [hA.spectral_theorem]
    simp [Unitary.conjStarAlgAut_apply, hUdef, Function.comp_def,
      Matrix.star_eq_conjTranspose]
  have hBeq : B = V * diagonal (fun i => ((hB.eigenvalues i : ℝ) : ℂ)) * Vᴴ := by
    conv_lhs => rw [hB.spectral_theorem]
    simp [Unitary.conjStarAlgAut_apply, hVdef, Function.comp_def,
      Matrix.star_eq_conjTranspose]
  obtain ⟨S, hS, htr⟩ := exists_doublyStochastic_trace_eq hU hU' hV hV' hAeq hBeq
  rw [htr]
  have hreindex : ∑ i, ∑ j, hA.eigenvalues i * S i j * hB.eigenvalues j
      = ∑ i, ∑ j, mu i * (S.submatrix sA sB) i j * nu j := by
    rw [← Equiv.sum_comp sA (fun i => ∑ j, hA.eigenvalues i * S i j * hB.eigenvalues j)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Equiv.sum_comp sB (fun j => hA.eigenvalues (sA i) * S (sA i) j * hB.eigenvalues j)]
    simp [hmu, hnu, Matrix.submatrix_apply]
  rw [hreindex]
  exact sum_mul_doublyStochastic_le
    (by simpa [Matrix.submatrix] using
      (reindex_mem_doublyStochastic (e₁ := sA.symm) (e₂ := sB.symm) hS)) hmu' hnu'

end Zeta23Redux.LinAlg

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

