import Mathlib

/-!
# Grover Optimal
Category: Frontier Qi
Target: QI.grover_optimal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

namespace QI

variable {N M : ℕ}

/-- The state space of a quantum query algorithm searching a database of size `N`:
an index register `Fin N` together with an arbitrary finite workspace `Fin M`. -/
abbrev State (N M : ℕ) : Type := EuclideanSpace ℂ (Fin N × Fin M)

/-- The standard phase oracle marking the index `i`: it flips the sign of every
amplitude whose index register holds `i`, and does nothing otherwise. -/

lemma norm_oracle_sub_self_sq (i : Fin N) (psi : State N M) :
    ‖oracle i psi - psi‖ ^ 2 = 4 * markSq i psi := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i]
  · simp only [markSq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    have : (oracle i psi - psi) (i, w) = -(2 * psi (i, w)) := by
      simp; ring
    rw [this]
    rw [norm_neg, norm_mul, mul_pow]
    norm_num
  · intro j _ hj
    refine Finset.sum_eq_zero fun w _ => ?_
    have : (oracle i psi - psi) (j, w) = 0 := by simp [hj]
    rw [this]
    simp
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- The state of the algorithm after `t` queries: the unitaries `U 0, U 1, …` are
arbitrary (they encode the whole algorithm) and `O` is the oracle being queried. -/
