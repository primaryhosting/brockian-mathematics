/-
# Cycle Laplacian Spectrum
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_laplacian_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to be the first command; the module docstring below
-- repeats the header verbatim.)
import Mathlib

/-!
# Cycle Laplacian Spectrum
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_laplacian_spectrum
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

open Matrix Polynomial

/-- The cyclic shift matrix on `ZMod n`: `shiftM n a i j = 1` exactly when `i - j = a`. -/

lemma shiftM_neg_one_pow (m : ℕ) : (shiftM n (-1)) ^ m = shiftM n (-(m : ZMod n)) := by
  induction m with
  | zero => simpa using (shiftM_zero (n := n)).symm
  | succ m ih =>
      rw [pow_succ, ih, shiftM_mul]
      congr 1
      push_cast
      ring

end Shift

section Distinct

variable {n : ℕ} [NeZero n]

/-- For `3 ≤ n`, `1 ≠ 0` in `ZMod n`. -/
