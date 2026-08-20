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

/-
# Data Processing
Category: Frontier Qi
Target: QI.data_processing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Data Processing

Category: Frontier Qi.  Target: `QI.data_processing`.

(The header above is repeated as a plain comment at the top of the file, since Lean does not
allow a module docstring to precede the `import` commands.)

## Quantum relative entropy and the data-processing inequality

We work with finite-dimensional quantum systems, i.e. complex matrices indexed by a finite
type `n`, and we use the Umegaki relative entropy
`D(ρ‖σ) = Tr[ρ (log ρ - log σ)]`,
where the matrix logarithm is the one provided by the continuous functional calculus.
-/

namespace QI

open Matrix Unitary
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The matrix logarithm, defined through the continuous functional calculus. -/

noncomputable def logm (A : Matrix n n ℂ) : Matrix n n ℂ := cfc Real.log A

/-- The Umegaki quantum relative entropy `D(ρ‖σ) = Tr[ρ (log ρ - log σ)]`. -/

noncomputable def relEntropy (ρ σ : Matrix n n ℂ) : ℝ := (ρ * (logm ρ - logm σ)).trace.re

/-- The dephasing (von Neumann measurement) channel associated with the standard basis:
it keeps the diagonal of a matrix and erases all off-diagonal entries. -/

def dephase (ρ : Matrix n n ℂ) : Matrix n n ℂ := diagonal (fun i => ρ i i)

section Basic

lemma logm_eq_conj (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    logm A = (hA.eigenvectorUnitary : Matrix n n ℂ) *
      diagonal (fun i => ((Real.log (hA.eigenvalues i) : ℝ) : ℂ)) *
      star (hA.eigenvectorUnitary : Matrix n n ℂ) := by
  rw [logm, hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  rfl

lemma spectral_eq_conj (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix n n ℂ) *
      diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) *
      star (hA.eigenvectorUnitary : Matrix n n ℂ) := by
  conv_lhs => rw [hA.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply]
  rfl

lemma trace_diag_mul_diag (a b : n → ℝ) (W : Matrix n n ℂ) :
    (diagonal (fun i => (a i : ℂ)) * W * diagonal (fun i => (b i : ℂ)) * Wᴴ).trace
      = ((∑ j, ∑ k, a j * b k * ‖W j k‖ ^ 2 : ℝ) : ℂ) := by
  have h1 : diagonal (fun i => (a i : ℂ)) * W * diagonal (fun i => (b i : ℂ))
      = Matrix.of (fun i j => (a i : ℂ) * W i j * (b j : ℂ)) := by
    ext i j
    simp [Matrix.mul_apply, Matrix.diagonal_apply, Finset.sum_ite_eq, mul_comm, mul_left_comm]
  rw [h1, Matrix.trace]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.of_apply, Matrix.conjTranspose_apply,
    RCLike.star_def]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show (a j : ℂ) * W j k * (b k : ℂ) * (starRingEnd ℂ) (W j k)
      = (a j : ℂ) * (b k : ℂ) * (W j k * (starRingEnd ℂ) (W j k)) by ring, Complex.mul_conj']

lemma trace_conj_mul_conj (u v : unitary (Matrix n n ℂ)) (A B : Matrix n n ℂ) :
    ((u : Matrix n n ℂ) * A * star (u : Matrix n n ℂ) *
      ((v : Matrix n n ℂ) * B * star (v : Matrix n n ℂ))).trace
      = (A * (star (u : Matrix n n ℂ) * v) * B *
          star (star (u : Matrix n n ℂ) * (v : Matrix n n ℂ))).trace := by
  rw [Matrix.star_mul, star_star]
  simp only [mul_assoc]
  rw [Matrix.trace_mul_comm]
  simp only [mul_assoc]

lemma sum_normSq_row (W : Matrix n n ℂ) (h : W * star W = 1) (j : n) :
    ∑ k, ‖W j k‖ ^ 2 = 1 := by
  have h1 := congrArg (fun M => M j j) h
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq, RCLike.star_def,
    Complex.mul_conj'] at h1
  exact_mod_cast h1

lemma sum_normSq_col (W : Matrix n n ℂ) (h : star W * W = 1) (k : n) :
    ∑ j, ‖W j k‖ ^ 2 = 1 := by
  have h1 := congrArg (fun M => M k k) h
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq, RCLike.star_def] at h1
  rw [show (∑ x, (starRingEnd ℂ) (W x k) * W x k) = ∑ x, W x k * (starRingEnd ℂ) (W x k) from
    Finset.sum_congr rfl fun x _ => mul_comm _ _] at h1
  simp only [Complex.mul_conj'] at h1
  exact_mod_cast h1

end Basic

section Klein

variable {ρ σ : Matrix n n ℂ}

/-- The doubly stochastic matrix of transition probabilities between the eigenbases of
`ρ` and `σ`. -/

noncomputable def transition (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (j k : n) : ℝ :=
  ‖(star (hρ.eigenvectorUnitary : Matrix n n ℂ) *
      (hσ.eigenvectorUnitary : Matrix n n ℂ)) j k‖ ^ 2

lemma transition_nonneg (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (j k : n) :
    0 ≤ transition hρ hσ j k := by
  unfold transition; positivity

/-- The matrix of overlaps between the two eigenbases is unitary. -/

lemma transitionMatrix_unitary (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    (star (hρ.eigenvectorUnitary : Matrix n n ℂ) * (hσ.eigenvectorUnitary : Matrix n n ℂ))
      ∈ unitary (Matrix n n ℂ) :=
  Submonoid.mul_mem _ (Unitary.star_mem hρ.eigenvectorUnitary.2) hσ.eigenvectorUnitary.2

lemma sum_transition_right (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (j : n) :
    ∑ k, transition hρ hσ j k = 1 :=
  sum_normSq_row _ (Unitary.mul_star_self_of_mem (transitionMatrix_unitary hρ hσ)) j

lemma sum_transition_left (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (k : n) :
    ∑ j, transition hρ hσ j k = 1 :=
  sum_normSq_col _ (Unitary.star_mul_self_of_mem (transitionMatrix_unitary hρ hσ)) k

lemma trace_mul_logm (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    (ρ * logm σ).trace
      = ((∑ j, ∑ k, hρ.eigenvalues j * Real.log (hσ.eigenvalues k) *
            transition hρ hσ j k : ℝ) : ℂ) := by
  conv_lhs => rw [spectral_eq_conj ρ hρ, logm_eq_conj σ hσ]
  rw [trace_conj_mul_conj]
  simp only [Matrix.star_eq_conjTranspose]
  rw [trace_diag_mul_diag]
  rfl

lemma trace_eq_sum_eigenvalues (hρ : ρ.IsHermitian) :
    ρ.trace = ((∑ j, hρ.eigenvalues j : ℝ) : ℂ) := by
  rw [hρ.trace_eq_sum_eigenvalues]
  push_cast
  rfl

lemma transition_self (hρ : ρ.IsHermitian) (j k : n) :
    transition hρ hρ j k = if j = k then 1 else 0 := by
  rw [transition, Unitary.star_mul_self_of_mem hρ.eigenvectorUnitary.2]
  rcases eq_or_ne j k with h | h
  · subst h; simp
  · simp [Matrix.one_apply_ne h, h]

lemma trace_mul_logm_self (hρ : ρ.IsHermitian) :
    (ρ * logm ρ).trace = ((∑ j, hρ.eigenvalues j * Real.log (hρ.eigenvalues j) : ℝ) : ℂ) := by
  rw [trace_mul_logm hρ hρ]
  norm_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [transition_self hρ, Finset.sum_ite_eq]

/-- The relative entropy written out in terms of eigenvalues and eigenbasis overlaps. -/

lemma relEntropy_eq_sum (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    relEntropy ρ σ = ∑ j, ∑ k, transition hρ hσ j k *
      (hρ.eigenvalues j * Real.log (hρ.eigenvalues j) -
        hρ.eigenvalues j * Real.log (hσ.eigenvalues k)) := by
  have hsplit : (ρ * (logm ρ - logm σ)).trace = (ρ * logm ρ).trace - (ρ * logm σ).trace := by
    rw [mul_sub, Matrix.trace_sub]
  rw [relEntropy, hsplit, trace_mul_logm_self hρ, trace_mul_logm hρ hσ]
  rw [← Complex.ofReal_sub, Complex.ofReal_re]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : ∑ k, transition hρ hσ j k * (hρ.eigenvalues j * Real.log (hρ.eigenvalues j) -
        hρ.eigenvalues j * Real.log (hσ.eigenvalues k))
      = (∑ k, transition hρ hσ j k) * (hρ.eigenvalues j * Real.log (hρ.eigenvalues j))
        - ∑ k, hρ.eigenvalues j * Real.log (hσ.eigenvalues k) * transition hρ hσ j k := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [h1, sum_transition_right hρ hσ, one_mul]

/-- Klein's inequality: `D(ρ‖σ) ≥ Tr ρ - Tr σ` for positive definite `ρ`, `σ`. -/

theorem relEntropy_ge_trace_sub (hρ : ρ.PosDef) (hσ : σ.PosDef) :
    ρ.trace.re - σ.trace.re ≤ relEntropy ρ σ := by
  have hρh := hρ.isHermitian
  have hσh := hσ.isHermitian
  have hl : ∀ j, 0 < hρh.eigenvalues j := fun j => hρ.eigenvalues_pos j
  have hm : ∀ k, 0 < hσh.eigenvalues k := fun k => hσ.eigenvalues_pos k
  rw [relEntropy_eq_sum hρh hσh]
  have key : ∀ j k, transition hρh hσh j k * (hρh.eigenvalues j - hσh.eigenvalues k)
      ≤ transition hρh hσh j k * (hρh.eigenvalues j * Real.log (hρh.eigenvalues j) -
          hρh.eigenvalues j * Real.log (hσh.eigenvalues k)) := by
    intro j k
    refine mul_le_mul_of_nonneg_left ?_ (transition_nonneg hρh hσh j k)
    have hlog := Real.log_le_sub_one_of_pos (div_pos (hm k) (hl j))
    rw [Real.log_div (hm k).ne' (hl j).ne'] at hlog
    have h2 := mul_le_mul_of_nonneg_left hlog (le_of_lt (hl j))
    have h3 : hρh.eigenvalues j * (hσh.eigenvalues k / hρh.eigenvalues j - 1)
        = hσh.eigenvalues k - hρh.eigenvalues j := by
      have hne : hρh.eigenvalues j ≠ 0 := (hl j).ne'
      field_simp
    have h4 : hρh.eigenvalues j *
          (Real.log (hσh.eigenvalues k) - Real.log (hρh.eigenvalues j))
        = hρh.eigenvalues j * Real.log (hσh.eigenvalues k)
          - hρh.eigenvalues j * Real.log (hρh.eigenvalues j) := by ring
    linarith
  calc ρ.trace.re - σ.trace.re
      = ∑ j, ∑ k, transition hρh hσh j k * (hρh.eigenvalues j - hσh.eigenvalues k) := by
        have e1 : ∑ j, ∑ k, transition hρh hσh j k * hρh.eigenvalues j
            = ∑ j, hρh.eigenvalues j := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← Finset.sum_mul, sum_transition_right hρh hσh, one_mul]
        have e2 : ∑ j, ∑ k, transition hρh hσh j k * hσh.eigenvalues k
            = ∑ k, hσh.eigenvalues k := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [← Finset.sum_mul, sum_transition_left hρh hσh, one_mul]
        rw [trace_eq_sum_eigenvalues hρh, trace_eq_sum_eigenvalues hσh, Complex.ofReal_re,
          Complex.ofReal_re, ← e1, ← e2, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
    _ ≤ _ := Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => key j k

/-- Klein's inequality: the relative entropy of two states with the same trace is
nonnegative. -/

theorem relEntropy_nonneg (hρ : ρ.PosDef) (hσ : σ.PosDef) (h : ρ.trace = σ.trace) :
    0 ≤ relEntropy ρ σ := by
  have := relEntropy_ge_trace_sub hρ hσ
  rw [h] at this
  simpa using this

end Klein

section Dephasing

variable {ρ σ : Matrix n n ℂ}

lemma dephase_isDiag (ρ : Matrix n n ℂ) : (dephase ρ).IsDiag := Matrix.isDiag_diagonal _

lemma dephase_posDef (hρ : ρ.PosDef) : (dephase ρ).PosDef :=
  Matrix.posDef_diagonal_iff.mpr fun _ => hρ.diag_pos

lemma trace_dephase (ρ : Matrix n n ℂ) : (dephase ρ).trace = ρ.trace := by
  simp [dephase, Matrix.trace, Matrix.diag_apply]

lemma dephase_of_isDiag (hσ : σ.IsDiag) : dephase σ = σ := by
  ext i j
  rcases eq_or_ne i j with h | h
  · subst h; simp [dephase]
  · simp [dephase, Matrix.diagonal_apply_ne _ h, hσ h]

/-- A matrix commuting with every diagonal matrix is itself diagonal. -/

lemma isDiag_of_commute_diagonal {M : Matrix n n ℂ}
    (h : ∀ d : n → ℂ, Commute M (diagonal d)) : M.IsDiag := by
  intro i j hij
  have := congrArg (fun N => N i j) (h (Pi.single j 1))
  simpa [Matrix.mul_apply, Matrix.diagonal_apply, Pi.single_apply, hij, Ne.symm hij] using this

/-- The logarithm of a diagonal positive definite matrix is diagonal. -/

lemma logm_isDiag (hd : σ.IsDiag) : (logm σ).IsDiag := by
  refine isDiag_of_commute_diagonal fun d => ?_
  have hcomm : Commute σ (diagonal d) := by
    have hσ' : σ = diagonal (fun i => σ i i) := (dephase_of_isDiag hd).symm
    rw [Commute, SemiconjBy, hσ', Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    exact congrArg _ (funext fun i => mul_comm _ _)
  exact (hcomm.cfc_real Real.log).symm.symm

/-- Only the diagonal of `ρ` matters when tracing against a diagonal matrix. -/

lemma trace_mul_of_isDiag (ρ X : Matrix n n ℂ) (hX : X.IsDiag) :
    (ρ * X).trace = (dephase ρ * X).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, dephase, Matrix.diagonal_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rcases eq_or_ne i j with h | h
  · subst h; simp
  · rw [hX (Ne.symm h)]
    simp [h]

lemma relEntropy_eq_sub (ρ σ : Matrix n n ℂ) :
    relEntropy ρ σ = (ρ * logm ρ).trace.re - (ρ * logm σ).trace.re := by
  rw [relEntropy, mul_sub, Matrix.trace_sub, Complex.sub_re]

/-- The Pythagorean identity: for a diagonal reference state `σ`, the relative entropy
splits as the sum of the entropy lost by dephasing and the relative entropy of the
dephased state. -/

theorem relEntropy_pythagoras (hd : σ.IsDiag) :
    relEntropy ρ σ = relEntropy ρ (dephase ρ) + relEntropy (dephase ρ) σ := by
  have h1 : (ρ * logm (dephase ρ)).trace = (dephase ρ * logm (dephase ρ)).trace :=
    trace_mul_of_isDiag _ _ (logm_isDiag (dephase_isDiag ρ))
  have h2 : (ρ * logm σ).trace = (dephase ρ * logm σ).trace :=
    trace_mul_of_isDiag _ _ (logm_isDiag hd)
  rw [relEntropy_eq_sub, relEntropy_eq_sub, relEntropy_eq_sub, h1, h2]
  ring

end Dephasing

/-- **Data-processing inequality** for the dephasing channel `dephase` (the von Neumann
measurement channel in the standard basis) and a reference state `σ` that is invariant
under it (i.e. is diagonal):

`D(Φ ρ ‖ Φ σ) ≤ D(ρ ‖ σ)`.
-/

theorem data_processing_dephase {ρ σ : Matrix n n ℂ} (hρ : ρ.PosDef) (hd : σ.IsDiag) :
    relEntropy (dephase ρ) (dephase σ) ≤ relEntropy ρ σ := by
  rw [dephase_of_isDiag hd, relEntropy_pythagoras (ρ := ρ) hd]
  have h0 : 0 ≤ relEntropy ρ (dephase ρ) :=
    relEntropy_nonneg hρ (dephase_posDef hρ) (trace_dephase ρ).symm
  linarith

section Measurement

variable {ρ σ : Matrix n n ℂ}

/-- Conjugation by a unitary commutes with the matrix logarithm. -/

noncomputable def measurement (u : unitary (Matrix n n ℂ)) (ρ : Matrix n n ℂ) :
    Matrix n n ℂ :=
  (u : Matrix n n ℂ) * dephase (star (u : Matrix n n ℂ) * ρ * (u : Matrix n n ℂ)) *
    star (u : Matrix n n ℂ)
