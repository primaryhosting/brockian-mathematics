import Mathlib

/-!
# Von Neumann Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.vonNeumann_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Matrix

namespace Zeta23Redux.LinAlg

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The squared moduli along a row of a unitary matrix sum to `1`. -/
lemma sum_sq_norm_row (T : Matrix n n ℂ) (h : T * Tᴴ = 1) (i : n) :
    ∑ j, ‖T i j‖ ^ 2 = 1 := by
  have h1 : (T * Tᴴ) i i = 1 := by rw [h]; simp
  have h2 : ((∑ j, ‖T i j‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← h1]; simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.mul_conj']
  exact_mod_cast h2

/-- The squared moduli along a column of a unitary matrix sum to `1`. -/
lemma sum_sq_norm_col (T : Matrix n n ℂ) (h : Tᴴ * T = 1) (j : n) :
    ∑ i, ‖T i j‖ ^ 2 = 1 := by
  have h1 : (Tᴴ * T) j j = 1 := by rw [h]; simp
  have h2 : ((∑ i, ‖T i j‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← h1]; simp [Matrix.mul_apply, Matrix.conjTranspose_apply, mul_comm, Complex.mul_conj']
  exact_mod_cast h2

/-- The basic bilinear identity: the trace of `diagonal lam * T * diagonal xi * Tᴴ` is the real
bilinear form in `lam` and `xi` given by the entrywise squared moduli of `T`. -/
lemma trace_diag_mul_diag (lam xi : n → ℝ) (T : Matrix n n ℂ) :
    (diagonal (fun i => (lam i : ℂ)) * T * diagonal (fun j => (xi j : ℂ)) * Tᴴ).trace
      = ((∑ i, ∑ j, lam i * xi j * ‖T i j‖ ^ 2 : ℝ) : ℂ) := by
  rw [Matrix.trace]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply,
    ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def]
  linear_combination ((lam i : ℂ) * (xi j : ℂ)) * Complex.mul_conj' (T i j)

/-- Rearrangement against a doubly stochastic matrix: for monovarying `mu`, `nu`, the bilinear
form `∑ i, ∑ j, mu i * nu j * S i j` is maximised at the identity.  This is Birkhoff's theorem
combined with the rearrangement inequality. -/
lemma sum_bilin_le_of_doublyStochastic (mu nu : n → ℝ) (hmn : Monovary mu nu)
    (S : Matrix n n ℝ) (hS : S ∈ doublyStochastic ℝ n) :
    ∑ i, ∑ j, mu i * nu j * S i j ≤ ∑ i, mu i * nu i := by
  obtain ⟨w, hw0, hw1, hwS⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hS
  have hSij : ∀ i j, S i j = ∑ σ : Equiv.Perm n, w σ * (σ.permMatrix ℝ) i j := by
    intro i j
    rw [← hwS]
    simp [Matrix.sum_apply]
  have hinner : ∀ (σ : Equiv.Perm n) (i : n),
      ∑ j, mu i * nu j * (w σ * (σ.permMatrix ℝ) i j) = w σ * (mu i * nu (σ i)) := by
    intro σ i
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, mul_comm,
      mul_left_comm]
  have key : ∑ i, ∑ j, mu i * nu j * S i j
      = ∑ σ : Equiv.Perm n, w σ * ∑ i, mu i * nu (σ i) := by
    calc ∑ i, ∑ j, mu i * nu j * S i j
        = ∑ i, ∑ j, ∑ σ : Equiv.Perm n, mu i * nu j * (w σ * (σ.permMatrix ℝ) i j) := by
          simp only [hSij, Finset.mul_sum]
      _ = ∑ i, ∑ σ : Equiv.Perm n, ∑ j, mu i * nu j * (w σ * (σ.permMatrix ℝ) i j) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ σ : Equiv.Perm n, ∑ i, ∑ j, mu i * nu j * (w σ * (σ.permMatrix ℝ) i j) :=
          Finset.sum_comm
      _ = ∑ σ : Equiv.Perm n, w σ * ∑ i, mu i * nu (σ i) := by
          refine Finset.sum_congr rfl fun σ _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => hinner σ i
  rw [key]
  calc ∑ σ : Equiv.Perm n, w σ * ∑ i, mu i * nu (σ i)
      ≤ ∑ _σ : Equiv.Perm n, w _σ * ∑ i, mu i * nu i :=
        Finset.sum_le_sum fun σ _ =>
          mul_le_mul_of_nonneg_left hmn.sum_mul_comp_perm_le_sum_mul (hw0 σ)
    _ = ∑ i, mu i * nu i := by rw [← Finset.sum_mul, hw1, one_mul]

/-- Von Neumann's trace inequality, in the form where the two Hermitian matrices are given
explicitly as unitary conjugates of real diagonal matrices, and `mu`, `nu` are arbitrary
rearrangements of the diagonals that monovary. -/
lemma vonNeumann_aux (U V : Matrix n n ℂ) (hUU : Uᴴ * U = 1) (hUU' : U * Uᴴ = 1)
    (hVV : Vᴴ * V = 1) (hVV' : V * Vᴴ = 1) (lam xi mu nu : n → ℝ) (sA sB : Equiv.Perm n)
    (hmu : mu = lam ∘ sA) (hnu : nu = xi ∘ sB) (hmn : Monovary mu nu) :
    ((U * diagonal (fun i => (lam i : ℂ)) * Uᴴ) *
      (V * diagonal (fun i => (xi i : ℂ)) * Vᴴ)).trace.re ≤ ∑ i, mu i * nu i := by
  set T : Matrix n n ℂ := Uᴴ * V with hTdef
  have hT : Tᴴ = Vᴴ * U := by simp [hTdef, Matrix.conjTranspose_mul]
  have hTT : T * Tᴴ = 1 := by
    rw [hT, hTdef]
    calc Uᴴ * V * (Vᴴ * U) = Uᴴ * (V * Vᴴ) * U := by simp [Matrix.mul_assoc]
      _ = 1 := by rw [hVV']; simp [hUU]
  have hTT' : Tᴴ * T = 1 := by
    rw [hT, hTdef]
    calc Vᴴ * U * (Uᴴ * V) = Vᴴ * (U * Uᴴ) * V := by simp [Matrix.mul_assoc]
      _ = 1 := by rw [hUU']; simp [hVV]
  have hX : (U * diagonal (fun i => (lam i : ℂ)) * Uᴴ) *
      (V * diagonal (fun i => (xi i : ℂ)) * Vᴴ)
      = U * (diagonal (fun i => (lam i : ℂ)) * (Uᴴ * V) *
          diagonal (fun i => (xi i : ℂ)) * Vᴴ) := by
    simp [Matrix.mul_assoc]
  have hXU : (diagonal (fun i => (lam i : ℂ)) * (Uᴴ * V) *
      diagonal (fun i => (xi i : ℂ)) * Vᴴ) * U
      = diagonal (fun i => (lam i : ℂ)) * T * diagonal (fun i => (xi i : ℂ)) * Tᴴ := by
    rw [hT, hTdef]; simp [Matrix.mul_assoc]
  have htr : ((U * diagonal (fun i => (lam i : ℂ)) * Uᴴ) *
      (V * diagonal (fun i => (xi i : ℂ)) * Vᴴ)).trace
      = ((∑ i, ∑ j, lam i * xi j * ‖T i j‖ ^ 2 : ℝ) : ℂ) := by
    rw [hX, Matrix.trace_mul_comm, hXU, trace_diag_mul_diag]
  rw [htr, Complex.ofReal_re]
  set S : Matrix n n ℝ := Matrix.of fun a b => ‖T (sA a) (sB b)‖ ^ 2 with hSdef
  have hSmem : S ∈ doublyStochastic ℝ n := by
    rw [mem_doublyStochastic_iff_sum]
    refine ⟨fun i j => ?_, fun a => ?_, fun b => ?_⟩
    · simp only [hSdef, Matrix.of_apply]
      positivity
    · have := Equiv.sum_comp sB (fun j => ‖T (sA a) j‖ ^ 2)
      simpa [hSdef] using this.trans (sum_sq_norm_row T hTT (sA a))
    · have := Equiv.sum_comp sA (fun i => ‖T i (sB b)‖ ^ 2)
      simpa [hSdef] using this.trans (sum_sq_norm_col T hTT' (sB b))
  have hreindex : ∑ i, ∑ j, lam i * xi j * ‖T i j‖ ^ 2 = ∑ a, ∑ b, mu a * nu b * S a b := by
    rw [← Equiv.sum_comp sA (fun i => ∑ j, lam i * xi j * ‖T i j‖ ^ 2)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Equiv.sum_comp sB (fun j => lam (sA a) * xi j * ‖T (sA a) j‖ ^ 2)]
    simp [hmu, hnu, hSdef]
  rw [hreindex]
  exact sum_bilin_le_of_doublyStochastic mu nu hmn S hSmem

/-- **Von Neumann's trace inequality** for Hermitian matrices.
If `mu` and `nu` list the eigenvalues of the Hermitian matrices `A` and `B` respectively,
both in the same (decreasing) order, then `Re (tr (A * B)) ≤ ∑ i, mu i * nu i`. -/
theorem vonNeumann_trace_ineq {d : ℕ} {A B : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (mu nu : Fin d → ℝ)
    (sA sB : Equiv.Perm (Fin d))
    (hmu : mu = hA.eigenvalues ∘ sA) (hnu : nu = hB.eigenvalues ∘ sB)
    (hmuAnti : Antitone mu) (hnuAnti : Antitone nu) :
    (A * B).trace.re ≤ ∑ i, mu i * nu i := by
  have hUU : (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)ᴴ *
      (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using
      Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.2
  have hUU' : (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) *
      (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)ᴴ = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using
      Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2
  have hVV : (hB.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)ᴴ *
      (hB.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using
      Unitary.star_mul_self_of_mem hB.eigenvectorUnitary.2
  have hVV' : (hB.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) *
      (hB.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)ᴴ = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using
      Unitary.mul_star_self_of_mem hB.eigenvectorUnitary.2
  have hAeq : A = (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) *
      diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) *
      (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)ᴴ := by
    conv_lhs => rw [hA.spectral_theorem]
    simp [Matrix.star_eq_conjTranspose, Function.comp_def]
  have hBeq : B = (hB.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) *
      diagonal (fun i => ((hB.eigenvalues i : ℝ) : ℂ)) *
      (hB.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)ᴴ := by
    conv_lhs => rw [hB.spectral_theorem]
    simp [Matrix.star_eq_conjTranspose, Function.comp_def]
  rw [hAeq, hBeq]
  exact vonNeumann_aux _ _ hUU hUU' hVV hVV' hA.eigenvalues hB.eigenvalues mu nu sA sB hmu hnu
    (hmuAnti.monovary hnuAnti)

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

