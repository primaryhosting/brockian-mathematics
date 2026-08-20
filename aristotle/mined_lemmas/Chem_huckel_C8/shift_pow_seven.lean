import Mathlib

/-!
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
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

namespace Chem

open Matrix Polynomial

/-- The adjacency matrix (over `ℂ`) of the cycle graph `C₈`; this is the Hückel matrix of
cyclooctatetraene in the units where the Coulomb integral is `0` and the resonance
integral is `1`. -/

lemma shift_pow_seven : shift ^ 7 = shiftInv := by
  have h : shift ^ 7 * (shift * shiftInv) = shift ^ 8 * shiftInv := by
    rw [← mul_assoc, ← pow_succ]
  rw [shift_mul_shiftInv, mul_one, shift_pow_eight, one_mul] at h
  exact h

/-- The adjacency matrix of `C₈` is the sum of the cyclic shift and its inverse. -/
