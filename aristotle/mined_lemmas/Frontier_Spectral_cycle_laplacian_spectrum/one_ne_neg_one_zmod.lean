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

lemma one_ne_neg_one_zmod (hn : 3 ≤ n) : (1 : ZMod n) ≠ -1 := by
  intro h
  have h3 : ((2 : ℕ) : ZMod n) = 0 := by push_cast; linear_combination h
  have h4 : (((2 : ℕ) : ZMod n)).val = 2 := ZMod.val_cast_of_lt (by omega)
  rw [h3, ZMod.val_zero] at h4
  exact absurd h4 (by norm_num)

/-- The entrywise identity behind `cycleLaplacian = 2·1 - S - S⁻¹`. -/
