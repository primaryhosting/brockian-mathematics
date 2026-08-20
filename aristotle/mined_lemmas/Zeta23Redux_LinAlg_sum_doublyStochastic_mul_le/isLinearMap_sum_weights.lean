/-
# Sum Doubly Stochastic Mul Le
Category: Linalg
Target: Zeta23Redux.LinAlg.sum_doublyStochastic_mul_le
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open Finset Matrix

namespace Zeta23Redux.LinAlg

/-- The linear functional `M ↦ ∑ i, ∑ j, M i j * (μ i * ν j)` is linear in the matrix `M`. -/

lemma isLinearMap_sum_weights {n : Type*} [Fintype n] (μ ν : n → ℝ) :
    IsLinearMap ℝ (fun M : Matrix n n ℝ => ∑ i, ∑ j, M i j * (μ i * ν j)) where
  map_add M N := by
    simp only [Matrix.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul c M := by
    simp only [Matrix.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

/-- Rearrangement step: for antitone weights, a permutation can only decrease the pairing. -/
