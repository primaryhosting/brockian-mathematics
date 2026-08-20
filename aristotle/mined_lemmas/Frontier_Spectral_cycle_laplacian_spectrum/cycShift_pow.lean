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
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier.Spectral

open Polynomial Matrix Complex

variable (n : ℕ) [NeZero n]

/-- The cyclic shift matrix on `ZMod n`: `(S *ᵥ v) i = v (i + 1)`. -/

lemma cycShift_pow (m : ℕ) :
    (cycShift n) ^ m = Matrix.of fun i j => if j = i + (m : ZMod n) then 1 else 0 := by
  induction m with
  | zero => ext i j; simp [Matrix.one_apply, eq_comm]
  | succ m ih =>
      ext i j
      rw [pow_succ, ih]
      simp only [Matrix.mul_apply, Matrix.of_apply, cycShift, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      push_cast
      rw [add_assoc]

