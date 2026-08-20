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
