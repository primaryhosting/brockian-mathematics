/-
# Von Neumann Trace Ineq Hermitian
Category: Brockian Corpus
Target: Zeta23Core.vonNeumann_trace_ineq_hermitian
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

namespace Zeta23Core

open Matrix Finset

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The matrix of squared absolute values of the entries of a unitary matrix is doubly
stochastic. -/

lemma sum_doublyStochastic_le {N : ℕ} {S : Matrix n n ℝ} (hS : S ∈ doublyStochastic ℝ n)
    (al be : n → ℝ) (a b : Fin N → ℝ) (ea eb : Fin N ≃ n)
    (ha : ∀ i, a i = al (ea i)) (hb : ∀ i, b i = be (eb i))
    (ha' : Antitone a) (hb' : Antitone b) :
    ∑ p, ∑ q, al p * be q * S p q ≤ ∑ i, a i * b i := by
  classical
  obtain ⟨w, hw0, hw1, hwS⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hS
  have hSentry : ∀ p q, S p q = ∑ σ : Equiv.Perm n, w σ * (if σ p = q then 1 else 0) := by
    intro p q
    rw [← hwS]
    simp [Matrix.sum_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
  have hperm : ∀ σ : Equiv.Perm n, ∑ p, al p * be (σ p) ≤ ∑ i, a i * b i := by
    intro σ
    have h1 : ∑ p, al p * be (σ p)
        = ∑ i, a i * b ((ea.trans (σ.trans eb.symm) : Equiv.Perm (Fin N)) i) := by
      refine (Fintype.sum_equiv ea _ _ ?_).symm
      intro i
      simp [ha, hb]
    rw [h1]
    simpa [smul_eq_mul] using
      (monovary_of_antitone ha' hb').sum_smul_comp_perm_le_sum_smul
        (σ := (ea.trans (σ.trans eb.symm) : Equiv.Perm (Fin N)))
  have hmain : ∑ p, ∑ q, al p * be q * S p q = ∑ σ : Equiv.Perm n, w σ * ∑ p, al p * be (σ p) := by
    calc ∑ p, ∑ q, al p * be q * S p q
        = ∑ p, ∑ σ : Equiv.Perm n, w σ * (al p * be (σ p)) := by
          refine Finset.sum_congr rfl fun p _ => ?_
          simp only [hSentry, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun σ _ => ?_
          simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
          ring
      _ = ∑ σ : Equiv.Perm n, w σ * ∑ p, al p * be (σ p) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun σ _ => (Finset.mul_sum _ _ _).symm
  rw [hmain]
  calc ∑ σ : Equiv.Perm n, w σ * ∑ p, al p * be (σ p)
      ≤ ∑ σ : Equiv.Perm n, w σ * ∑ i, a i * b i :=
        Finset.sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left (hperm σ) (hw0 σ)
    _ = ∑ i, a i * b i := by rw [← Finset.sum_mul, hw1, one_mul]

/--
**Von Neumann trace inequality, Hermitian case.**

If `A` and `B` are Hermitian matrices over an `RCLike` field indexed by a finite type `n`, and
`a`, `b : Fin N → ℝ` list the eigenvalues of `A` and `B` respectively (i.e. each is the family of
eigenvalues reindexed by an equivalence `Fin N ≃ n`) in decreasing order, then
`Re tr(A * B) ≤ ∑ i, a i * b i`.
-/
