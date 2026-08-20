/-
# Expander Uniform Gap Witness
Category: Frontier Spectral
Target: Frontier.Spectral.expander_uniform_gap_witness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open Matrix

set_option maxHeartbeats 1000000

namespace Frontier.Spectral

/-! ## The hypercube graph -/

/-- The vertex set of the `k`-dimensional hypercube: binary strings of length `k`. -/
abbrev Cube (k : ℕ) := Fin k → ZMod 2


lemma two_isLapEigenvalue {k : ℕ} (hk : 1 ≤ k) : IsLapEigenvalue k 2 := by
  classical
  set i0 : Fin k := ⟨0, hk⟩ with hi0
  refine ⟨fun x => if x i0 = 0 then (1:ℝ) else -1, ?_, ?_⟩
  · intro hcon
    have hval := congrFun hcon (fun _ => 0)
    simp at hval
  · funext x
    set c : ℝ := if x i0 = 0 then (1:ℝ) else -1 with hc
    have hflip : ∀ i : Fin k, (if flipAt i x i0 = 0 then (1:ℝ) else -1)
        = if i = i0 then -c else c := by
      intro i
      by_cases hi : i = i0
      · rw [if_pos hi, hi, flipAt_apply_self, hc]
        have hval : x i0 = 0 ∨ x i0 = 1 := by
          generalize x i0 = a
          revert a
          decide
        rcases hval with hx | hx
        · rw [hx, show ((0 : ZMod 2) + 1) = 1 from by decide,
            if_neg (by decide : ¬((1 : ZMod 2) = 0)), if_pos rfl]
        · rw [hx, show ((1 : ZMod 2) + 1) = 0 from by decide, if_pos rfl,
            if_neg (by decide : ¬((1 : ZMod 2) = 0))]
          norm_num
      · rw [if_neg hi, flipAt_apply_of_ne (Ne.symm hi)]
    rw [SimpleGraph.lapMatrix_mulVec_apply, sum_neighbors, degree_hypercube]
    simp only [hflip]
    have hsum : ∑ i : Fin k, (if i = i0 then -c else c) = (k : ℝ) * c - 2 * c := by
      have hterm : ∀ i : Fin k, (if i = i0 then -c else c) = c + (if i = i0 then -2*c else 0) := by
        intro i
        by_cases hi : i = i0
        · simp [hi]; ring
        · simp [hi]
      rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib,
        Finset.sum_ite_eq' Finset.univ i0 (fun _ => -2*c), Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, if_pos (Finset.mem_univ i0)]
      ring
    rw [hsum]
    simp only [Pi.smul_apply, smul_eq_mul]
    show (k : ℝ) * c - ((k : ℝ) * c - 2 * c) = 2 * c
    ring

/-- **Expander uniform gap witness.**

For every `k ≥ 1`, the smallest nonzero eigenvalue of the Laplacian of the hypercube
graph `Q_k` (on `2^k` vertices) is exactly `2`.  Since the bound `2` does not depend on
`k`, the family `(Q_k)_{k ≥ 1}` has a uniform spectral gap. -/
