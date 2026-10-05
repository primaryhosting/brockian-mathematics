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

lemma shift_pow (k : ℕ) : shift n ^ k = Matrix.circulant (Pi.single ((k : ZMod n)) 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, shift, Matrix.circulant_mul]
    congr 1
    funext i
    rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (1 : ZMod n)]
    · rw [Matrix.circulant_apply, Pi.single_eq_same, mul_one, Pi.single_apply, Pi.single_apply]
      push_cast
      simp [sub_eq_iff_eq_add]
    · intro b _ hb; simp [Pi.single_apply, hb]
    · simp

