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

lemma cycleLaplacian_mulVec_fiedlerVec {n : ℕ} [NeZero n] (hn : 3 ≤ n) :
    cycleLaplacian n *ᵥ fiedlerVec n = (2 - 2 * Real.cos (2 * Real.pi / n)) • fiedlerVec n := by
  funext i
  rw [cycleLaplacian_mulVec hn, fiedlerVec_eigen hn i]
  simp

/-! ## Main theorem -/

/-- **Fiedler value of the cycle.**  For `n ≥ 3`, the algebraic connectivity (second smallest
Laplacian eigenvalue) of the cycle graph `C n` equals `2 - 2 cos (2π/n)`. -/
