import Mathlib

/-!
# Cos Trace Norm 4001
Category: Brockian Corpus
Target: Brockian.CosTraceNorm4001
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

open Finset

/-- The `4001 × 4001` cosine-difference (Gram) matrix attached to a family of phases
`θ : Fin 4001 → ℝ`, given by `G i j = cos (θ i - θ j)`. -/

lemma cosGram4001_quadForm (θ x : Fin 4001 → ℝ) :
    ∑ i, ∑ j, x i * x j * cosGram4001 θ i j
      = (∑ i, x i * Real.cos (θ i)) ^ 2 + (∑ i, x i * Real.sin (θ i)) ^ 2 := by
  have h : ∀ i j : Fin 4001, x i * x j * cosGram4001 θ i j
      = (x i * Real.cos (θ i)) * (x j * Real.cos (θ j))
        + (x i * Real.sin (θ i)) * (x j * Real.sin (θ j)) := by
    intro i j
    simp only [cosGram4001, Matrix.of_apply, Real.cos_sub]
    ring
  calc ∑ i, ∑ j, x i * x j * cosGram4001 θ i j
      = ∑ i, ∑ j, ((x i * Real.cos (θ i)) * (x j * Real.cos (θ j))
          + (x i * Real.sin (θ i)) * (x j * Real.sin (θ j))) := by
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => h i j
    _ = (∑ i, ∑ j, (x i * Real.cos (θ i)) * (x j * Real.cos (θ j)))
          + ∑ i, ∑ j, (x i * Real.sin (θ i)) * (x j * Real.sin (θ j)) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib
    _ = (∑ i, x i * Real.cos (θ i)) ^ 2 + (∑ i, x i * Real.sin (θ i)) ^ 2 := by
        rw [sq, sq, Finset.sum_mul_sum, Finset.sum_mul_sum]

/-- **Cos Trace Norm 4001.**

For every family of phases `θ : Fin 4001 → ℝ`, the cosine-difference matrix
`G i j = cos (θ i - θ j)` is symmetric and positive semidefinite, its trace equals `4001`,
and its quadratic form is bounded by `4001 * ‖x‖²`.  Consequently `G` has trace norm exactly
`4001` (its trace, since it is positive semidefinite) while its operator norm is at most `4001`. -/
