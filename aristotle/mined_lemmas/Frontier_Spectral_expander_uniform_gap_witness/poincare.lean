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


lemma poincare (k : ℕ) (f : Cube k → ℝ) (hf : ∑ x : Cube k, f x = 0) :
    4 * ∑ x : Cube k, (f x) ^ 2 ≤ Dir k f := by
  induction k with
  | zero =>
    have hall : ∀ x : Cube 0, f x = 0 := by
      intro x
      rw [← Fintype.sum_subsingleton f x]
      exact hf
    simp [Dir, hall]
  | succ k ih =>
    set g : Cube k → ℝ := fun y => f (Fin.cons 0 y) with hg
    set h : Cube k → ℝ := fun y => f (Fin.cons 1 y) with hh
    have hsum : ∑ y : Cube k, (g + h) y = 0 := by
      rw [← hf, sum_cube_succ f]
      exact Finset.sum_congr rfl fun y _ => rfl
    have hIH : 4 * ∑ y : Cube k, ((g + h) y) ^ 2 ≤ Dir k (g + h) := ih _ hsum
    have hpar : Dir k (g + h) / 2 ≤ Dir k g + Dir k h := Dir_add_le g h
    have hlhs : ∑ x : Cube (k+1), (f x) ^ 2
        = ∑ y : Cube k, ((g y) ^ 2 + (h y) ^ 2) := sum_cube_succ (fun x => (f x) ^ 2)
    have hDir : Dir (k+1) f = Dir k g + Dir k h + 2 * ∑ y : Cube k, (g y - h y) ^ 2 :=
      Dir_succ f
    have hpt : 2 * ∑ y : Cube k, ((g + h) y) ^ 2 + 2 * ∑ y : Cube k, (g y - h y) ^ 2
        = 4 * ∑ y : Cube k, ((g y) ^ 2 + (h y) ^ 2) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun y _ => ?_
      simp only [Pi.add_apply]
      ring
    rw [hlhs, hDir]
    nlinarith [hIH, hpar, hpt]

/-! ## The Laplacian quadratic form -/

