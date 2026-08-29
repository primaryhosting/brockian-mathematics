import Mathlib

/-!
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real
open Complex Matrix

namespace Chem

/-- A primitive 19-th root of unity. -/

lemma adj_mul_F : (SimpleGraph.cycleGraph 19).adjMatrix ℂ * F19 = F19 * D19 := by
  ext i k
  have hLHS : ((SimpleGraph.cycleGraph 19).adjMatrix ℂ * F19) i k
      = ∑ j ∈ (SimpleGraph.cycleGraph 19).neighborFinset i, F19 j k := by
    rw [Matrix.mul_apply]
    have := SimpleGraph.adjMatrix_mulVec_apply (α := ℂ) (SimpleGraph.cycleGraph 19) i
      (fun j => F19 j k)
    simpa [Matrix.mulVec, dotProduct] using this
  have hnb : (SimpleGraph.cycleGraph 19).neighborFinset i = {i - 1, i + 1} :=
    SimpleGraph.cycleGraph_neighborFinset (n := 17) (v := i)
  have hne : (i - 1 : Fin 19) ≠ i + 1 := by
    intro h
    rw [sub_eq_add_neg, add_right_inj] at h
    exact absurd h (by decide)
  rw [hLHS, hnb, Finset.sum_pair hne]
  simp only [D19]
  rw [Matrix.mul_diagonal]
  set w : ℂ := omega19 ^ (k : ℕ) with hw
  have hw19 : w ^ 19 = 1 := by
    rw [hw]
    exact pow_pow_19 _ omega19_pow _
  have hw0 : w ≠ 0 := pow_ne_zero _ omega19_ne_zero
  have hF : ∀ j : Fin 19, F19 j k = w ^ (j : ℕ) := by
    intro j
    simp only [F19, Matrix.of_apply, hw, pow_mul']
  rw [hF, hF, hF, pow_val_pred w hw19 hw0, pow_val_succ w hw19, ← omega_pow_add_inv k, ← hw]
  ring

