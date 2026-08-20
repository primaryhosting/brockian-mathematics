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


lemma quadratic_form_eq {k : ℕ} (f : Cube k → ℝ) :
    ∑ x : Cube k, f x * ((hypercube k).lapMatrix ℝ *ᵥ f) x = Dir k f / 2 := by
  have h1 : ∑ x : Cube k, f x * ((hypercube k).lapMatrix ℝ *ᵥ f) x
      = (∑ x : Cube k, ∑ _i : Fin k, (f x) ^ 2)
        - (∑ x : Cube k, ∑ i : Fin k, f x * f (flipAt i x)) := by
    rw [sum_sum_sub]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [SimpleGraph.lapMatrix_mulVec_apply, sum_neighbors, degree_hypercube,
      Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← Finset.mul_sum]
    ring
  have h2 : Dir k f
      = (∑ x : Cube k, ∑ _i : Fin k, (f x) ^ 2)
        - 2 * (∑ x : Cube k, ∑ i : Fin k, f x * f (flipAt i x))
        + (∑ x : Cube k, ∑ i : Fin k, (f (flipAt i x)) ^ 2) := by
    rw [sum_sum_mul, sum_sum_sub, sum_sum_add, Dir]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => by ring
  rw [h1, h2, sum_flip_sq]
  ring

/-! ## Eigenvalues of the hypercube Laplacian -/

/-- `μ` is an eigenvalue of the Laplacian of the `k`-dimensional hypercube. -/
