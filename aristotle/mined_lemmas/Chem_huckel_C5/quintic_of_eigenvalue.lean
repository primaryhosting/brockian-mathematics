/-
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Matrix Real

namespace Chem

/-- The adjacency matrix of the cycle graph `C₅` (the Hückel matrix of cyclopentadienyl
with `α = 0`, `β = 1`), with vertices `0,1,2,3,4` arranged in a pentagon. -/

lemma quintic_of_eigenvalue {μ : ℝ} {v : Fin 5 → ℝ} (hv : v ≠ 0) (h : C5adj *ᵥ v = μ • v) :
    μ ^ 5 - 5 * μ ^ 3 + 5 * μ - 2 = 0 := by
  have key : ∀ n : ℕ, C5adj ^ n *ᵥ v = μ ^ n • v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul, pow_succ,
          mul_comm]
  have h5 := key 5
  rw [C5adj_pow_five] at h5
  have h3 := key 3
  simp only [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at h5
  rw [h3, h] at h5
  have : (μ ^ 5 - 5 * μ ^ 3 + 5 * μ - 2) • v = 0 := by
    calc (μ ^ 5 - 5 * μ ^ 3 + 5 * μ - 2) • v
        = μ ^ 5 • v - ((5:ℝ) • μ ^ 3 • v - (5:ℝ) • (μ • v) + (2:ℝ) • v) := by module
      _ = 0 := by rw [h5, sub_self]
  rcases smul_eq_zero.mp this with h | h
  · exact h
  · exact absurd h hv

/-- Explicit eigenvectors: `2` is an eigenvalue, and so is any root of `x² + x - 1`. -/
