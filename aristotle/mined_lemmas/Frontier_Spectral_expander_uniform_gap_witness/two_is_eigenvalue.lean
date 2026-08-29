/-
# Expander Uniform Gap Witness
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.expander_uniform_gap_witness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Expander Uniform Gap Witness
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.expander_uniform_gap_witness
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

open Finset Matrix SimpleGraph

/-- The vertex set of the `k`-dimensional hypercube: bit strings of length `k`. -/
abbrev Cube (k : ℕ) := Fin k → ZMod 2

/-- The `i`-th standard basis vector of the cube (the string with a single `1` in place `i`). -/

lemma two_is_eigenvalue {k : ℕ} (hk : 1 ≤ k) :
    ∃ v : Cube k → ℝ, v ≠ 0 ∧ (hypercube k).lapMatrix ℝ *ᵥ v = (2 : ℝ) • v := by
  have hk0 : 0 < k := hk
  set i0 : Fin k := ⟨0, hk0⟩ with hi0
  refine ⟨fun x => if x i0 = 0 then (1 : ℝ) else -1, ?_, ?_⟩
  · intro h
    have h0 := congrFun h (0 : Cube k)
    simp at h0
  · funext x
    set c : ℝ := if x i0 = 0 then (1 : ℝ) else -1 with hc
    have hcases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
    have key : ∀ i : Fin k,
        (if (x + cubeE i) i0 = 0 then (1 : ℝ) else -1) = c - (if i = i0 then 2 * c else 0) := by
      intro i
      have h01 : (0 : ZMod 2) + 1 = 1 := by decide
      have h11 : (1 : ZMod 2) + 1 = 0 := by decide
      by_cases hi : i = i0
      · have hx : (x + cubeE i) i0 = x i0 + 1 := by simp [cubeE, hi]
        rw [hx, if_pos hi, hc]
        rcases hcases (x i0) with h | h <;> rw [h] <;> simp only [h01, h11] <;> norm_num
      · have hx : (x + cubeE i) i0 = x i0 := by
          simp [cubeE, hi]
        simp [hx, hi, hc]
    rw [lapMatrix_hypercube_mulVec_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_congr rfl (fun i _ => key i), Finset.sum_sub_distrib, Finset.sum_const,
      Finset.sum_ite_eq' Finset.univ i0 (fun _ => 2 * c), if_pos (Finset.mem_univ i0),
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring

/-- **Uniform spectral gap for the hypercube family.**
For every `k ≥ 1`, the smallest nonzero eigenvalue of the Laplacian of the hypercube
graph `Q k` on `2 ^ k` vertices is exactly `2`, independently of `k`. -/
