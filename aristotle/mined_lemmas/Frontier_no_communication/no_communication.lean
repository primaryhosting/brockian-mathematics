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

theorem no_communication (ρ : Matrix (m × n) (m × n) ℂ) (K : ι → Matrix n n ℂ)
    (hK : ∑ a, (K a)ᴴ * (K a) = 1) :
    ptraceB (applyB K ρ) = ptraceB ρ := by
  ext i j
  have step : (ptraceB (applyB K ρ)) i j
      = ∑ b, ∑ d, ∑ a, ∑ k,
          K a k b * ρ (i, b) (j, d) * (starRingEnd ℂ) (K a k d) := by
    rw [← sum_reorder (fun k a b d => K a k b * ρ (i, b) (j, d) * (starRingEnd ℂ) (K a k d))]
    simp only [ptraceB, applyB, Matrix.sum_apply]
    exact Finset.sum_congr rfl fun k _ =>
      Finset.sum_congr rfl fun a _ => localB_conj_apply ρ (K a) i j k
  rw [step]
  have inner : ∀ b d : n,
      (∑ a, ∑ k, K a k b * ρ (i, b) (j, d) * (starRingEnd ℂ) (K a k d))
        = ρ (i, b) (j, d) * (∑ a, ((K a)ᴴ * (K a)) d b) := by
    intro b d
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Matrix.conjTranspose_apply, RCLike.star_def]
    ring
  simp only [inner]
  have : ∀ (d b : n), (∑ a, ((K a)ᴴ * (K a)) d b) = (1 : Matrix n n ℂ) d b := by
    intro d b
    rw [← hK]
    simp [Matrix.sum_apply]
  simp only [this, ptraceB]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp [Matrix.one_apply]

/-- Specialization to a unitary local operation: if Bob applies a unitary `U` to his half,
Alice's reduced state is unchanged. -/
