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

lemma laplacian_entry_identity (h10 : (1 : ZMod n) ≠ 0) (h1n : (1 : ZMod n) ≠ -1)
    (d : ZMod n) :
    (2 : ℂ) * (if d = 0 then 1 else 0) - (if d = -1 then 1 else 0) - (if d = 1 then 1 else 0)
      = if d = 0 then (2 : ℂ) else if d = 1 ∨ d = -1 then -1 else 0 := by
  have h0n : (0 : ZMod n) ≠ -1 := fun h => h10 (by linear_combination h)
  by_cases h0 : d = 0
  · subst h0
    simp [Ne.symm h10, h0n]
  · by_cases h1 : d = 1
    · subst h1
      simp [h10, h1n]
    · by_cases hm : d = -1
      · subst hm
        simp [h0, h1]
      · simp [h0, h1, hm]

/-- The cycle Laplacian is the polynomial `2 - X - X^(n-1)` evaluated at the cyclic shift. -/
