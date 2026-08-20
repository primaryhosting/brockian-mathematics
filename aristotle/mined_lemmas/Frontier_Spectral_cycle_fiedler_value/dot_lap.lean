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
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier.Spectral

open Finset Matrix

namespace CycleAux

variable (m : ℕ)

/-- The primitive `(m+3)`-rd root of unity. -/

lemma dot_lap (x : Fin (m + 3) → ℝ) :
    x ⬝ᵥ ((SimpleGraph.cycleGraph (m + 3)).lapMatrix ℝ *ᵥ x)
      = ∑ i : Fin (m + 3), (x i - x (i + 1)) ^ 2 := by
  have h1 : ∑ i : Fin (m + 3), x (i + 1) ^ 2 = ∑ i : Fin (m + 3), x i ^ 2 :=
    shift_sum m (fun j => x j ^ 2)
  have h2 : ∑ i : Fin (m + 3), x (i + 1) * x (i + 1 - 1) = ∑ i : Fin (m + 3), x i * x (i - 1) :=
    shift_sum m (fun j => x j * x (j - 1))
  simp only [add_sub_cancel_right] at h2
  simp only [dotProduct, lap_mulVec]
  have hexp : ∀ i : Fin (m + 3), x i * (2 * x i - x (i - 1) - x (i + 1))
      = 2 * x i ^ 2 - x i * x (i - 1) - x i * x (i + 1) := fun i => by ring
  simp only [hexp, Finset.sum_sub_distrib]
  have h3 : ∀ i : Fin (m + 3), (x i - x (i + 1)) ^ 2
      = x i ^ 2 + x (i + 1) ^ 2 - 2 * (x i * x (i + 1)) := fun i => by ring
  simp only [h3, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [h1]
  have h4 : ∑ i : Fin (m + 3), x i * x (i - 1) = ∑ i : Fin (m + 3), x i * x (i + 1) := by
    rw [← h2]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h4]
  ring

