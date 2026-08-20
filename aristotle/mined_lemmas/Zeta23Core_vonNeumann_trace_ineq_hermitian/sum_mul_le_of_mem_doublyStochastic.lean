import Mathlib

/-!
# Von Neumann Trace Ineq Hermitian
Category: Brockian Corpus
Target: Zeta23Core.vonNeumann_trace_ineq_hermitian
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
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option grind.warning false

namespace Zeta23Core

open Matrix Finset

section DoublyStochastic

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
/-- Two antitone functions monovary. -/

theorem sum_mul_le_of_mem_doublyStochastic {a b : n → ℝ} (hab : Monovary a b)
    {D : Matrix n n ℝ} (hD : D ∈ doublyStochastic ℝ n) :
    ∑ j, ∑ k, D j k * (a j * b k) ≤ ∑ i, a i * b i := by
  have hlin : IsLinearMap ℝ (fun M : Matrix n n ℝ => ∑ j, ∑ k, M j k * (a j * b k)) := by
    constructor
    · intro M N
      simp [Matrix.add_apply, add_mul, Finset.sum_add_distrib]
    · intro c M
      simp [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  have hmem : D ∈ {M : Matrix n n ℝ |
      (fun M : Matrix n n ℝ => ∑ j, ∑ k, M j k * (a j * b k)) M ≤ ∑ i, a i * b i} := by
    rw [← SetLike.mem_coe, doublyStochastic_eq_convexHull_permMatrix] at hD
    refine convexHull_min ?_ (convex_halfSpace_le hlin _) hD
    rintro _ ⟨σ, rfl⟩
    simp only [Set.mem_setOf_eq]
    have key : ∀ j : n, ∑ k, (σ.permMatrix ℝ) j k * (a j * b k) = a j • b (σ j) := by
      intro j
      simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv, smul_eq_mul]
    rw [Finset.sum_congr rfl fun j _ => key j]
    exact hab.sum_smul_comp_perm_le_sum_smul
  exact hmem

/-- The matrix of squared absolute values of the entries of a unitary matrix is doubly
stochastic. -/
