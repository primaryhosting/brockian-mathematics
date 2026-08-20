/-
# Sum Doubly Stochastic Mul Le
Category: Linalg
Target: Zeta23Redux.LinAlg.sum_doublyStochastic_mul_le
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open Finset Matrix

namespace Zeta23Redux.LinAlg

/-- The linear functional `M ↦ ∑ i, ∑ j, M i j * (μ i * ν j)` is linear in the matrix `M`. -/

lemma sum_permMatrix_mul_le {n : Type*} [Fintype n] [LinearOrder n] [DecidableEq n]
    (σ : Equiv.Perm n) {μ ν : n → ℝ} (hμ : Antitone μ) (hν : Antitone ν) :
    ∑ i, ∑ j, (σ.permMatrix ℝ) i j * (μ i * ν j) ≤ ∑ i, μ i * ν i := by
  have hsum : ∑ i, ∑ j, (σ.permMatrix ℝ) i j * (μ i * ν j) = ∑ i, μ i * ν (σ i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp
  rw [hsum]
  simpa using (hμ.monovary hν).sum_smul_comp_perm_le_sum_smul (σ := σ)

/--
**Doubly stochastic rearrangement bound.**
If `S` is doubly stochastic and `μ`, `ν` are antitone weight sequences, then
`∑ i, ∑ j, S i j * (μ i * ν j) ≤ ∑ i, μ i * ν i`.
This is the Birkhoff/rearrangement step feeding the von Neumann trace inequality.
-/
