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
