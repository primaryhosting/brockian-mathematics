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

lemma fiedlerVec_mem_rayleighSet {n : ℕ} [NeZero n] (hn : 3 ≤ n) :
    (2 - 2 * Real.cos (2 * Real.pi / n)) ∈ rayleighSet n := by
  refine ⟨fiedlerVec n, fiedlerVec_ne_zero, fiedlerVec_sum hn, ?_⟩
  have hpos : 0 < fiedlerVec n ⬝ᵥ fiedlerVec n := dotProduct_self_pos fiedlerVec_ne_zero
  have hQ : fiedlerVec n ⬝ᵥ (cycleLaplacian n *ᵥ fiedlerVec n)
      = (2 - 2 * Real.cos (2 * Real.pi / n)) * (fiedlerVec n ⬝ᵥ fiedlerVec n) := by
    rw [dotProduct, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [cycleLaplacian_mulVec hn _ i, fiedlerVec_eigen hn i]
    ring
  rw [hQ]
  field_simp

/-- The all-ones vector spans the kernel direction: `0` is a Laplacian eigenvalue. -/
