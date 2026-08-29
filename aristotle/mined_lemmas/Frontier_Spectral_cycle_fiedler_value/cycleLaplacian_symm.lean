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

lemma cycleLaplacian_symm (i j : ZMod n) : cycleLaplacian n i j = cycleLaplacian n j i := by
  unfold cycleLaplacian
  have hiff : (j = i + 1 ∨ j = i - 1) ↔ (i = j + 1 ∨ i = j - 1) := by
    constructor
    · rintro (h | h)
      · exact Or.inr (by rw [h]; ring)
      · exact Or.inl (by rw [h]; ring)
    · rintro (h | h)
      · exact Or.inr (by rw [h]; ring)
      · exact Or.inl (by rw [h]; ring)
  by_cases h : i = j
  · simp [h]
  · simp [h, Ne.symm h, hiff]

/-- The all-ones vector lies in the kernel of the cycle Laplacian: the row sums vanish. -/
