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


open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Zeta23Redux.LinAlg

open Matrix Finset

variable {d : ℕ}

/-- The rearrangement step: for antitone `mu`, `nu` and a permutation `σ`,
`∑ i, mu i * nu (σ i) ≤ ∑ i, mu i * nu i`. -/
lemma sum_mul_comp_perm_le (mu nu : Fin d → ℝ) (hmu : Antitone mu) (hnu : Antitone nu)
    (σ : Equiv.Perm (Fin d)) :
    ∑ i, mu i * nu (σ i) ≤ ∑ i, mu i * nu i := by
  have hmono : Monovary nu mu := by
    intro i j hij
    have hji : j < i := by
      by_contra h
      exact absurd (hmu (not_lt.1 h)) (not_le.2 hij)
    exact hnu hji.le
  simpa [smul_eq_mul, mul_comm] using hmono.sum_comp_perm_smul_le_sum_smul (σ := σ)

/-- Bilinear bound against a doubly stochastic matrix: if `mu` and `nu` are both antitone
and `S` is doubly stochastic, then `∑ i j, mu i * nu j * S i j ≤ ∑ i, mu i * nu i`.
This is where Birkhoff's theorem enters. -/
lemma sum_bilin_le_of_doublyStochastic (mu nu : Fin d → ℝ)
    (hmu : Antitone mu) (hnu : Antitone nu)
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S ∈ doublyStochastic ℝ (Fin d)) :
    ∑ i, ∑ j, mu i * nu j * S i j ≤ ∑ i, mu i * nu i := by
  obtain ⟨w, hw0, hw1, hwS⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hS
  have expand : ∀ i j : Fin d,
      S i j = ∑ σ : Equiv.Perm (Fin d), w σ * (if σ i = j then 1 else 0) := by
    intro i j
    rw [← hwS]
    simp [Matrix.sum_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
  have step1 : ∀ i : Fin d, ∑ j, mu i * nu j * S i j
      = ∑ σ : Equiv.Perm (Fin d), w σ * (mu i * nu (σ i)) := by
    intro i
    have hj : ∀ j : Fin d, mu i * nu j * S i j
        = ∑ σ : Equiv.Perm (Fin d), (mu i * nu j * w σ) * (if σ i = j then 1 else 0) := by
      intro j; rw [expand i j, Finset.mul_sum]; ring_nf
    rw [Finset.sum_congr rfl fun j _ => hj j, Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp [Finset.sum_ite_eq, mul_comm, mul_left_comm]
  calc ∑ i, ∑ j, mu i * nu j * S i j
      = ∑ σ : Equiv.Perm (Fin d), w σ * ∑ i, mu i * nu (σ i) := by
        rw [Finset.sum_congr rfl fun i _ => step1 i, Finset.sum_comm]
        exact Finset.sum_congr rfl fun σ _ => (Finset.mul_sum _ _ _).symm
    _ ≤ ∑ σ : Equiv.Perm (Fin d), w σ * ∑ i, mu i * nu i :=
        Finset.sum_le_sum fun σ _ =>
          mul_le_mul_of_nonneg_left (sum_mul_comp_perm_le mu nu hmu hnu σ) (hw0 σ)
    _ = ∑ i, mu i * nu i := by rw [← Finset.sum_mul, hw1, one_mul]

/-- Doubly stochastic matrices are stable under reindexing rows and columns by permutations. -/
lemma submatrix_mem_doublyStochastic (S : Matrix (Fin d) (Fin d) ℝ)
    (hS : S ∈ doublyStochastic ℝ (Fin d)) (e f : Equiv.Perm (Fin d)) :
    S.submatrix e f ∈ doublyStochastic ℝ (Fin d) := by
  rw [mem_doublyStochastic_iff_sum] at hS ⊢
  obtain ⟨h0, hr, hc⟩ := hS
  refine ⟨fun i j => h0 _ _, fun i => ?_, fun j => ?_⟩
  · rw [show (∑ j, S.submatrix e f i j) = ∑ j, S (e i) (f j) from rfl, Equiv.sum_comp f (S (e i))]
    exact hr _
  · rw [show (∑ i, S.submatrix e f i j) = ∑ i, S (e i) (f j) from rfl,
      Equiv.sum_comp e (fun i => S i (f j))]
    exact hc _

/-- The entrywise squared modulus of a unitary matrix is doubly stochastic. -/
lemma normSq_mem_doublyStochastic (W : Matrix (Fin d) (Fin d) ℂ)
    (hW : W ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    (Matrix.of fun i j => Complex.normSq (W i j)) ∈ doublyStochastic ℝ (Fin d) := by
  have h1 : W * star W = 1 := hW.2
  have h2 : star W * W = 1 := hW.1
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨fun i j => Complex.normSq_nonneg _, ?_, ?_⟩
  · intro i
    have h := congrFun (congrFun h1 i) i
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at h
    have h' : (∑ j, W i j * (starRingEnd ℂ) (W i j)) = 1 := by simpa [RCLike.star_def] using h
    have hre := congrArg Complex.re h'
    rw [Complex.re_sum] at hre
    simpa [Complex.mul_conj, Complex.normSq] using hre
  · intro j
    have h := congrFun (congrFun h2 j) j
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at h
    have h' : (∑ i, W i j * (starRingEnd ℂ) (W i j)) = 1 := by
      rw [← h]; exact Finset.sum_congr rfl fun i _ => by simp [RCLike.star_def, mul_comm]
    have hre := congrArg Complex.re h'
    rw [Complex.re_sum] at hre
    simpa [Complex.mul_conj, Complex.normSq] using hre

/-- Trace formula after diagonalisation:
`tr (diag mu * W * diag nu * W*) = ∑ i j, mu i * nu j * |W i j|²`. -/
lemma trace_diag_mul_diag (mu nu : Fin d → ℝ) (W : Matrix (Fin d) (Fin d) ℂ) :
    Matrix.trace (diagonal (RCLike.ofReal ∘ mu : Fin d → ℂ) * W *
        diagonal (RCLike.ofReal ∘ nu : Fin d → ℂ) * star W)
      = ((∑ i, ∑ j, mu i * nu j * Complex.normSq (W i j) : ℝ) : ℂ) := by
  rw [mul_assoc (diagonal (RCLike.ofReal ∘ mu : Fin d → ℂ) * W)
      (diagonal (RCLike.ofReal ∘ nu : Fin d → ℂ)) (star W)]
  rw [Matrix.trace]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.diagonal_mul, Matrix.diagonal_mul, Matrix.star_apply]
  simp only [Function.comp_apply, RCLike.ofReal_alg]
  rw [← Complex.mul_conj]
  simp [RCLike.star_def]
  ring

/-- **Von Neumann's trace inequality** for Hermitian complex matrices.

If `A`, `B` are Hermitian `d × d` complex matrices and `mu`, `nu` list the eigenvalues of
`A` and `B` respectively (each a permutation of the Mathlib eigenvalue list), both in
decreasing (antitone) order, then `Re (tr (A * B)) ≤ ∑ i, mu i * nu i`. -/
theorem vonNeumann_trace_ineq {A B : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (mu nu : Fin d → ℝ) (hmu : Antitone mu) (hnu : Antitone nu)
    (hmuA : ∃ e : Equiv.Perm (Fin d), mu = hA.eigenvalues ∘ e)
    (hnuB : ∃ e : Equiv.Perm (Fin d), nu = hB.eigenvalues ∘ e) :
    (Matrix.trace (A * B)).re ≤ ∑ i, mu i * nu i := by
  obtain ⟨eA, hmuA⟩ := hmuA
  obtain ⟨eB, hnuB⟩ := hnuB
  set U : Matrix (Fin d) (Fin d) ℂ := (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) with hUdef
  set V : Matrix (Fin d) (Fin d) ℂ := (hB.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) with hVdef
  have hU1 : U * star U = 1 := hA.eigenvectorUnitary.2.2
  have hU2 : star U * U = 1 := hA.eigenvectorUnitary.2.1
  have hV1 : V * star V = 1 := hB.eigenvectorUnitary.2.2
  have hV2 : star V * V = 1 := hB.eigenvectorUnitary.2.1
  set W : Matrix (Fin d) (Fin d) ℂ := star U * V with hWdef
  have hstarW : star W = star V * U := by rw [hWdef, Matrix.star_mul, star_star]
  have hWmem : W ∈ Matrix.unitaryGroup (Fin d) ℂ := by
    constructor
    · rw [hstarW, hWdef,
        show star V * U * (star U * V) = star V * (U * star U) * V by simp [mul_assoc], hU1]
      simp [hV2]
    · rw [hstarW, hWdef,
        show star U * V * (star V * U) = star U * (V * star V) * U by simp [mul_assoc], hV1]
      simp [hU2]
  -- the eigenvalue lists provided by Mathlib
  set p : Fin d → ℝ := hA.eigenvalues with hpdef
  set q : Fin d → ℝ := hB.eigenvalues with hqdef
  -- reduce the product to a conjugate of a "diagonal sandwich"
  have hAspec : A = U * diagonal (RCLike.ofReal ∘ p) * star U := hA.spectral_theorem
  have hBspec : B = V * diagonal (RCLike.ofReal ∘ q) * star V := hB.spectral_theorem
  have key : A * B =
      U * (diagonal (RCLike.ofReal ∘ p) * W * diagonal (RCLike.ofReal ∘ q) * star W) * star U := by
    rw [hstarW, hWdef]
    conv_lhs => rw [hAspec, hBspec]
    simp only [mul_assoc]
    rw [hU1, mul_one]
  -- the trace is a conjugation-invariant, so it equals the trace of the sandwich
  have htr : Matrix.trace (A * B) =
      Matrix.trace (diagonal (RCLike.ofReal ∘ p) * W * diagonal (RCLike.ofReal ∘ q) * star W) := by
    rw [key, Matrix.trace_mul_comm, ← mul_assoc, hU2, one_mul]
  -- the doubly stochastic matrix
  set S : Matrix (Fin d) (Fin d) ℝ := Matrix.of fun i j => Complex.normSq (W i j) with hSdef
  have hSds : S ∈ doublyStochastic ℝ (Fin d) := normSq_mem_doublyStochastic W hWmem
  have htr2 : (Matrix.trace (A * B)).re = ∑ i, ∑ j, p i * q j * S i j := by
    rw [htr, trace_diag_mul_diag p q W, Complex.ofReal_re]
    rfl
  -- reindex by the two permutations
  have hreindex : ∑ i, ∑ j, p i * q j * S i j
      = ∑ i, ∑ j, mu i * nu j * (S.submatrix eA eB) i j := by
    rw [← Equiv.sum_comp eA (fun i => ∑ j, p i * q j * S i j)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Equiv.sum_comp eB (fun j => p (eA i) * q j * S (eA i) j)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hmuA, hnuB]
    rfl
  rw [htr2, hreindex]
  exact sum_bilin_le_of_doublyStochastic mu nu hmu hnu _
    (submatrix_mem_doublyStochastic S hSds eA eB)

/-- Any finite family of reals can be permuted into decreasing order. -/
lemma exists_antitone_perm (f : Fin d → ℝ) : ∃ e : Equiv.Perm (Fin d), Antitone (f ∘ e) := by
  refine ⟨Tuple.sort (fun i => -f i), ?_⟩
  have h := Tuple.monotone_sort (fun i => -f i)
  intro i j hij
  have hij' := h hij
  simp only [Function.comp_apply] at hij' ⊢
  linarith

/-- The hypotheses of `vonNeumann_trace_ineq` are satisfiable: every Hermitian matrix admits
a decreasing enumeration of its eigenvalues. -/
theorem exists_antitone_eigenvalue_enumeration {A : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) :
    ∃ mu : Fin d → ℝ, Antitone mu ∧ ∃ e : Equiv.Perm (Fin d), mu = hA.eigenvalues ∘ e := by
  obtain ⟨e, he⟩ := exists_antitone_perm hA.eigenvalues
  exact ⟨hA.eigenvalues ∘ e, he, e, rfl⟩

end Zeta23Redux.LinAlg

