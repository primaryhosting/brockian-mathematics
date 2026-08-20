/-
# Cycle Fiedler Value
Category: Frontier Spectral
Target: Frontier.Spectral.cycle_fiedler_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring `/-! ... -/`, so the mandated
-- header above is written as a plain block comment; its text is verbatim.)

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

set_option grind.warning false

namespace Frontier.Spectral

open Finset Complex ZMod Matrix

/-! ## The Laplacian of the cycle graph -/

/-- The Laplacian matrix of the cycle graph `C n`, with vertex set `ZMod n`:
`2` on the diagonal, `-1` between neighbours `i` and `i ± 1`, `0` elsewhere. -/

lemma cycle_quadratic_form {n : ℕ} [NeZero n] (hn : 3 ≤ n) (x : ZMod n → ℝ) :
    x ⬝ᵥ (cycleLaplacian n *ᵥ x) = ∑ j, (x j - x (j + 1)) ^ 2 := by
  have hstep : x ⬝ᵥ (cycleLaplacian n *ᵥ x)
      = ∑ i : ZMod n, x i * (2 * x i - x (i + 1) - x (i - 1)) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [cycleLaplacian_mulVec hn x i]
  rw [hstep]
  have e1 : ∑ i : ZMod n, x (i + 1) ^ 2 = ∑ i : ZMod n, x i ^ 2 := sum_shift (fun j => x j ^ 2)
  have e2 : ∑ i : ZMod n, x i * x (i - 1) = ∑ i : ZMod n, x i * x (i + 1) := by
    have h := sum_shift (fun j => x j * x (j - 1))
    simp only [add_sub_cancel_right] at h
    rw [← h]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  have L : ∑ i : ZMod n, x i * (2 * x i - x (i + 1) - x (i - 1))
      = 2 * (∑ i : ZMod n, x i ^ 2) - (∑ i : ZMod n, x i * x (i + 1))
        - ∑ i : ZMod n, x i * x (i - 1) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have R : ∑ j : ZMod n, (x j - x (j + 1)) ^ 2
      = (∑ i : ZMod n, x i ^ 2) - 2 * (∑ i : ZMod n, x i * x (i + 1))
        + ∑ i : ZMod n, x (i + 1) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [L, R, e1, e2]
  ring

/-! ## The Fiedler eigenvector -/

/-- The candidate Fiedler eigenvector `j ↦ cos (2π j / n)`. -/
