/-
# Von Neumann Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.vonNeumann_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators
open Matrix Finset

namespace Zeta23Redux.LinAlg

variable {d : ℕ}

/-- The entrywise squared modulus of a unitary matrix is doubly stochastic. -/
lemma normSq_unitary_mem_doublyStochastic {W : Matrix (Fin d) (Fin d) ℂ}
    (hW : W ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    (Matrix.of fun p q => Complex.normSq (W p q)) ∈ doublyStochastic ℝ (Fin d) := by
  have h1 : W * star W = 1 := Matrix.mem_unitaryGroup_iff.mp hW
  have h2 : star W * W = 1 := Matrix.mem_unitaryGroup_iff'.mp hW
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨fun i j => Complex.normSq_nonneg _, fun p => ?_, fun q => ?_⟩
  · have h := congrFun (congrFun h1 p) p
    simp [Matrix.mul_apply, Complex.mul_conj] at h
    exact_mod_cast h
  · have h := congrFun (congrFun h2 q) q
    simp [Matrix.mul_apply, mul_comm, Complex.mul_conj] at h
    exact_mod_cast h

/-- Birkhoff + rearrangement: a bilinear form of two antitone vectors against a doubly
stochastic matrix is bounded by the aligned pairing. -/
lemma sum_mul_doublyStochastic_le {mu nu : Fin d → ℝ} (hmu : Antitone mu) (hnu : Antitone nu)
    {S : Matrix (Fin d) (Fin d) ℝ} (hS : S ∈ doublyStochastic ℝ (Fin d)) :
    ∑ p, ∑ q, mu p * nu q * S p q ≤ ∑ i, mu i * nu i := by
  obtain ⟨w, hw0, hw1, hwS⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hS
  have hmono : Monovary nu mu := by
    intro i j h
    rcases le_or_gt i j with hij | hij
    · exact absurd (hmu hij) (not_le.2 h)
    · exact hnu hij.le
  have key : ∀ σ : Equiv.Perm (Fin d), ∑ p, mu p * nu (σ p) ≤ ∑ i, mu i * nu i := by
    intro σ
    have := hmono.sum_comp_perm_mul_le_sum_mul (σ := σ)
    simpa [mul_comm] using this
  have hSpq : ∀ p q, S p q = ∑ σ : Equiv.Perm (Fin d), if q = σ p then w σ else 0 := by
    intro p q
    rw [← hwS]
    simp [Matrix.sum_apply, Matrix.smul_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
      Equiv.toPEquiv_apply, eq_comm]
  have step : ∀ p, ∑ q, mu p * nu q * S p q
      = ∑ σ : Equiv.Perm (Fin d), w σ * (mu p * nu (σ p)) := by
    intro p
    simp_rw [hSpq, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp [mul_ite, Finset.sum_ite_eq']
    ring
  calc ∑ p, ∑ q, mu p * nu q * S p q
      = ∑ σ : Equiv.Perm (Fin d), w σ * ∑ p, mu p * nu (σ p) := by
        simp_rw [step, Finset.mul_sum]
        rw [Finset.sum_comm]
    _ ≤ ∑ σ : Equiv.Perm (Fin d), w σ * ∑ i, mu i * nu i :=
        Finset.sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left (key σ) (hw0 σ)
    _ = ∑ i, mu i * nu i := by rw [← Finset.sum_mul, hw1, one_mul]

/-- Version of `sum_mul_doublyStochastic_le` where the two vectors are arbitrary
rearrangements of the antitone ones. -/
lemma sum_mul_doublyStochastic_le_of_perm {mu nu alpha beta : Fin d → ℝ}
    (hmu : Antitone mu) (hnu : Antitone nu)
    (halpha : ∃ σ : Equiv.Perm (Fin d), mu = alpha ∘ σ)
    (hbeta : ∃ τ : Equiv.Perm (Fin d), nu = beta ∘ τ)
    {S : Matrix (Fin d) (Fin d) ℝ} (hS : S ∈ doublyStochastic ℝ (Fin d)) :
    ∑ p, ∑ q, alpha p * beta q * S p q ≤ ∑ i, mu i * nu i := by
  obtain ⟨σ, hσ⟩ := halpha
  obtain ⟨τ, hτ⟩ := hbeta
  have hS' : S.submatrix σ τ ∈ doublyStochastic ℝ (Fin d) := by
    have := reindex_mem_doublyStochastic (e₁ := σ.symm) (e₂ := τ.symm) hS
    simpa [Matrix.reindex_apply] using this
  have heq : ∑ p, ∑ q, alpha p * beta q * S p q
      = ∑ i, ∑ j, mu i * nu j * (S.submatrix σ τ) i j := by
    rw [← Equiv.sum_comp σ (fun p => ∑ q, alpha p * beta q * S p q)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Equiv.sum_comp τ (fun q => alpha (σ i) * beta q * S (σ i) q)]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [hσ, hτ, Matrix.submatrix_apply]
  rw [heq]
  exact sum_mul_doublyStochastic_le hmu hnu hS'

/-- The trace of a product of two diagonalised Hermitian matrices, expanded against the
squared moduli of the entries of the connecting unitary. -/
lemma trace_mul_conj_diagonal (alpha beta : Fin d → ℝ)
    {U V : Matrix (Fin d) (Fin d) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    Matrix.trace ((U * Matrix.diagonal (fun i => (alpha i : ℂ)) * star U) *
        (V * Matrix.diagonal (fun i => (beta i : ℂ)) * star V))
      = ((∑ p, ∑ q, alpha p * beta q * Complex.normSq ((star U * V) p q) : ℝ) : ℂ) := by
  set Da := Matrix.diagonal (fun i => (alpha i : ℂ)) with hDa
  set Db := Matrix.diagonal (fun i => (beta i : ℂ)) with hDb
  set W := star U * V with hW
  have hUU : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have hstarW : star W = star V * U := by
    rw [hW, Matrix.star_mul, star_star]
  have hfact : (U * Da * star U) * (V * Db * star V) = U * (Da * W * Db * star W) * star U := by
    rw [hstarW, hW]
    have h1 : U * (Da * (star U * V) * Db * (star V * U)) * star U
        = U * Da * (star U * V) * Db * (star V * (U * star U)) := by
      simp [mul_assoc]
    rw [h1, hUU, mul_one]
    simp [mul_assoc]
  rw [hfact, Matrix.trace_mul_comm, ← mul_assoc,
    show star U * U = 1 from Matrix.mem_unitaryGroup_iff'.mp hU, one_mul]
  have hentry : ∀ p, (Da * W * Db * star W) p p
      = ((∑ q, alpha p * beta q * Complex.normSq (W p q) : ℝ) : ℂ) := by
    intro p
    rw [Matrix.mul_apply]
    push_cast
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.star_apply, Complex.star_def,
      ← Complex.mul_conj]
    ring
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, hentry]
  push_cast
  rfl

/-- **Von Neumann's trace inequality** for Hermitian matrices: if `mu` and `nu` list the
eigenvalues of the Hermitian matrices `A` and `B` in decreasing order, then
`Re (trace (A * B)) ≤ ∑ i, mu i * nu i`. -/
theorem vonNeumann_trace_ineq {A B : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (mu nu : Fin d → ℝ)
    (hmu : Antitone mu) (hnu : Antitone nu)
    (hmuA : ∃ σ : Equiv.Perm (Fin d), mu = hA.eigenvalues ∘ σ)
    (hnuB : ∃ τ : Equiv.Perm (Fin d), nu = hB.eigenvalues ∘ τ) :
    (Matrix.trace (A * B)).re ≤ ∑ i, mu i * nu i := by
  set U : Matrix (Fin d) (Fin d) ℂ := ↑hA.eigenvectorUnitary with hUdef
  set V : Matrix (Fin d) (Fin d) ℂ := ↑hB.eigenvectorUnitary with hVdef
  have hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ := hA.eigenvectorUnitary.2
  have hV : V ∈ Matrix.unitaryGroup (Fin d) ℂ := hB.eigenvectorUnitary.2
  have hAeq : A = U * Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) * star U := by
    have h := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    exact h
  have hBeq : B = V * Matrix.diagonal (fun i => (hB.eigenvalues i : ℂ)) * star V := by
    have h := hB.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    exact h
  have hW : star U * V ∈ Matrix.unitaryGroup (Fin d) ℂ :=
    Submonoid.mul_mem _ (Unitary.star_mem hU) hV
  have htrace : Matrix.trace (A * B)
      = ((∑ p, ∑ q, hA.eigenvalues p * hB.eigenvalues q *
          Complex.normSq ((star U * V) p q) : ℝ) : ℂ) := by
    conv_lhs => rw [hAeq, hBeq]
    exact trace_mul_conj_diagonal _ _ hU
  rw [htrace, Complex.ofReal_re]
  exact sum_mul_doublyStochastic_le_of_perm hmu hnu hmuA hnuB
    (normSq_unitary_mem_doublyStochastic hW)

/-- Any real tuple admits an antitone (decreasing) rearrangement. -/
lemma exists_antitone_rearrangement (f : Fin d → ℝ) :
    ∃ mu : Fin d → ℝ, Antitone mu ∧ ∃ σ : Equiv.Perm (Fin d), mu = f ∘ σ := by
  refine ⟨f ∘ Tuple.sort f ∘ Fin.rev, ?_, (Fin.revPerm).trans (Tuple.sort f), rfl⟩
  intro i j hij
  exact Tuple.monotone_sort f (Fin.rev_le_rev.mpr hij)

/-- Von Neumann's trace inequality, stated with the explicit decreasing rearrangements of the
eigenvalues of `A` and `B`. -/
theorem vonNeumann_trace_ineq_sorted {A B : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (Matrix.trace (A * B)).re ≤
      ∑ i, (hA.eigenvalues ∘ Tuple.sort hA.eigenvalues ∘ Fin.rev) i *
        (hB.eigenvalues ∘ Tuple.sort hB.eigenvalues ∘ Fin.rev) i := by
  refine vonNeumann_trace_ineq hA hB _ _ ?_ ?_
    ⟨(Fin.revPerm).trans (Tuple.sort hA.eigenvalues), rfl⟩
    ⟨(Fin.revPerm).trans (Tuple.sort hB.eigenvalues), rfl⟩
  · exact fun i j hij => Tuple.monotone_sort hA.eigenvalues (Fin.rev_le_rev.mpr hij)
  · exact fun i j hij => Tuple.monotone_sort hB.eigenvalues (Fin.rev_le_rev.mpr hij)

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

