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

variable {n : ℕ} [NeZero n]

/-- The cyclic shift matrix on `ZMod n`: `shift n i j = 1` iff `i - j = 1`. -/

lemma cast_pred_eq_neg_one (hn : 1 ≤ n) : ((n - 1 : ℕ) : ZMod n) = -1 := by
  have h : (((n - 1 : ℕ) : ZMod n) + 1 : ZMod n) = 0 := by
    have hc : ((n - 1 : ℕ) : ZMod n) + ((1 : ℕ) : ZMod n) = ((n - 1 + 1 : ℕ) : ZMod n) := by
      push_cast; ring
    rw [Nat.cast_one] at hc
    rw [hc, Nat.sub_add_cancel hn, ZMod.natCast_self]
  linear_combination h

/-- The cycle Laplacian is the polynomial `2 - X - X ^ (n-1)` evaluated at the shift matrix. -/
