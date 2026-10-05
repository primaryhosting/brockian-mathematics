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

lemma norm_one_sub_sq {z : ℂ} (h : ‖z‖ = 1) : ‖1 - z‖ ^ 2 = 2 - 2 * z.re := by
  have h' : Complex.normSq z = 1 := by rw [← Complex.sq_norm, h]; norm_num
  rw [Complex.sq_norm]
  simp [Complex.normSq_apply] at h' ⊢
  nlinarith [h']

end Character

section Fourier

open scoped ZMod

variable {N : ℕ} [NeZero N]

/-- Parseval's identity for the discrete Fourier transform on `ZMod N`. -/
