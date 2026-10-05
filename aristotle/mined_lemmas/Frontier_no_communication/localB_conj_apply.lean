import Mathlib

/-!
# No Communication
Category: Frontier Physics
Target: Frontier.no_communication
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Matrix Kronecker

namespace Frontier

variable {m n ι : Type*} [Fintype m] [Fintype n] [Fintype ι] [DecidableEq m] [DecidableEq n]

/-- The reduced state ("partial trace") of a bipartite density matrix on the `m`-factor
(Alice's system), obtained by tracing out the `n`-factor (Bob's system). -/

private lemma localB_conj_apply (ρ : Matrix (m × n) (m × n) ℂ) (K : Matrix n n ℂ) (i j : m)
    (k : n) :
    (localB K * ρ * (localB K)ᴴ : Matrix (m × n) (m × n) ℂ) (i, k) (j, k)
      = ∑ b, ∑ d, K k b * ρ (i, b) (j, d) * (starRingEnd ℂ) (K k d) := by
  simp only [localB]
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, Fintype.sum_prod_type,
    ite_mul, Finset.sum_mul, apply_ite (starRingEnd ℂ), mul_ite]
  rw [Finset.sum_comm]

/-- **No communication theorem.**

If Bob applies an arbitrary quantum channel to his half of a bipartite system — i.e. a trace
preserving family of Kraus operators `K a` acting as `1 ⊗ K a`, with `∑ a, (K a)ᴴ * (K a) = 1` —
then Alice's reduced density matrix is completely unchanged.  Since every statistic Alice can
observe is a function of her reduced state, Bob's local operation transmits no information. -/
