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


lemma Dir_succ {k : ℕ} (f : Cube (k+1) → ℝ) :
    Dir (k+1) f
      = Dir k (fun y => f (Fin.cons 0 y)) + Dir k (fun y => f (Fin.cons 1 y))
        + 2 * ∑ y : Cube k, (f (Fin.cons 0 y) - f (Fin.cons 1 y)) ^ 2 := by
  rw [Dir, sum_cube_succ]
  have key : ∀ (a : ZMod 2) (y : Cube k),
      ∑ i : Fin (k+1), (f (Fin.cons a y) - f (flipAt i (Fin.cons a y))) ^ 2
        = (f (Fin.cons a y) - f (Fin.cons (a+1) y)) ^ 2
          + ∑ i : Fin k, (f (Fin.cons a y) - f (Fin.cons a (flipAt i y))) ^ 2 := by
    intro a y
    rw [Fin.sum_univ_succ, flipAt_zero_cons]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by rw [flipAt_succ_cons]
  simp only [key]
  rw [show (0 : ZMod 2) + 1 = 1 from by decide, show (1 : ZMod 2) + 1 = 0 from by decide]
  rw [Dir, Dir, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  have hs : (f (Fin.cons 1 y) - f (Fin.cons 0 y)) ^ 2
      = (f (Fin.cons 0 y) - f (Fin.cons 1 y)) ^ 2 := by ring
  rw [hs]
  ring

/-- **Poincaré inequality for the hypercube.** For any mean-zero function the Dirichlet
form dominates `4` times the squared `ℓ²`-norm. -/
