import Mathlib
/-!
# Cycle Fiedler Value
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_fiedler_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

open Finset ZMod

/-- The Laplacian matrix of the cycle graph `C n` on the vertex set `ZMod n`:
diagonal entries `2` (each vertex has degree `2`), and `-1` in position `(i, j)`
whenever `j = i + 1` or `j = i - 1`. -/

lemma cycleLaplacian_quadratic_form (h3 : 3 ≤ n) (v : ZMod n → ℝ) :
    ∑ i : ZMod n, v i * (cycleLaplacian n).mulVec v i
      = ∑ i : ZMod n, (v i - v (i + 1)) ^ 2 := by
  have hshift1 : ∑ i : ZMod n, v (i + 1) ^ 2 = ∑ i : ZMod n, v i ^ 2 :=
    sum_shift (fun i => v i ^ 2) 1
  have hshift2 : ∑ i : ZMod n, v i * v (i - 1) = ∑ i : ZMod n, v i * v (i + 1) := by
    have := sum_shift (fun i => v i * v (i - 1)) 1
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [mul_comm]
  have hL : ∀ i : ZMod n, v i * (cycleLaplacian n).mulVec v i
      = 2 * v i ^ 2 - v i * v (i + 1) - v i * v (i - 1) := by
    intro i
    rw [cycleLaplacian_mulVec h3]
    ring
  have e1 : ∑ i : ZMod n, v i * (cycleLaplacian n).mulVec v i
      = 2 * (∑ i : ZMod n, v i ^ 2) - (∑ i : ZMod n, v i * v (i + 1))
        - ∑ i : ZMod n, v i * v (i + 1) := by
    simp only [hL]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hshift2, ← Finset.mul_sum]
  have e2 : ∑ i : ZMod n, (v i - v (i + 1)) ^ 2
      = (∑ i : ZMod n, v i ^ 2) - 2 * (∑ i : ZMod n, v i * v (i + 1))
        + ∑ i : ZMod n, v (i + 1) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e1, e2, hshift1]
  ring

end Basic

section Character

variable {N : ℕ} [NeZero N]

/-- The standard additive character has modulus one, so complex conjugation inverts it. -/
