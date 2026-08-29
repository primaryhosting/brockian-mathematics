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
noncomputable def cosGram4001 (θ : Fin 4001 → ℝ) : Matrix (Fin 4001) (Fin 4001) ℝ :=
  Matrix.of fun i j => Real.cos (θ i - θ j)

/-- The quadratic form of the cosine-difference matrix is a sum of two squares. -/
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
theorem CosTraceNorm4001 (θ : Fin 4001 → ℝ) :
    (∀ i j, cosGram4001 θ i j = cosGram4001 θ j i) ∧
    (cosGram4001 θ).trace = 4001 ∧
    (∀ x : Fin 4001 → ℝ, 0 ≤ ∑ i, ∑ j, x i * x j * cosGram4001 θ i j) ∧
    (∀ x : Fin 4001 → ℝ,
      ∑ i, ∑ j, x i * x j * cosGram4001 θ i j ≤ 4001 * ∑ i, (x i) ^ 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j
    simp only [cosGram4001, Matrix.of_apply, ← Real.cos_neg (θ i - θ j)]
    ring_nf
  · simp [Matrix.trace, Matrix.diag, cosGram4001]
  · intro x
    rw [cosGram4001_quadForm]
    positivity
  · intro x
    rw [cosGram4001_quadForm]
    have hc : (∑ i, x i * Real.cos (θ i)) ^ 2
        ≤ (∑ i, (x i) ^ 2) * ∑ i, (Real.cos (θ i)) ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    have hs : (∑ i, x i * Real.sin (θ i)) ^ 2
        ≤ (∑ i, (x i) ^ 2) * ∑ i, (Real.sin (θ i)) ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    have hsum : (∑ i, (Real.cos (θ i)) ^ 2) + ∑ i, (Real.sin (θ i)) ^ 2 = 4001 := by
      rw [← Finset.sum_add_distrib]
      simp [Real.cos_sq_add_sin_sq]
    calc (∑ i, x i * Real.cos (θ i)) ^ 2 + (∑ i, x i * Real.sin (θ i)) ^ 2
        ≤ (∑ i, (x i) ^ 2) * (∑ i, (Real.cos (θ i)) ^ 2)
            + (∑ i, (x i) ^ 2) * ∑ i, (Real.sin (θ i)) ^ 2 := add_le_add hc hs
      _ = (∑ i, (x i) ^ 2) * ((∑ i, (Real.cos (θ i)) ^ 2) + ∑ i, (Real.sin (θ i)) ^ 2) := by
          ring
      _ = 4001 * ∑ i, (x i) ^ 2 := by rw [hsum]; ring

end Brockian

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

