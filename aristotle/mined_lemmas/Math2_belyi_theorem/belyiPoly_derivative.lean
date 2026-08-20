import Mathlib

/-!
# Belyi Theorem
Category: Frontier Math
Target: Math2.belyi_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000

open Polynomial IntermediateField

namespace Math2

/-- A complex number is a *rational point* if it lies in the image of `ℚ`. -/

lemma belyiPoly_derivative (a b : ℕ) :
    derivative (belyiPoly a b) =
      C (belyiConst a b) *
        (X ^ a * ((1 - X) ^ b * (C ((a : ℚ) + 1) - C ((a : ℚ) + b + 2) * X))) := by
  unfold belyiPoly
  rw [derivative_mul, derivative_C, zero_mul, zero_add, derivative_mul, derivative_X_pow,
    derivative_pow]
  simp only [Nat.add_sub_cancel, derivative_sub, derivative_one, derivative_X, zero_sub,
    Nat.cast_add, Nat.cast_one, C_add, C_1, map_natCast, C_ofNat]
  ring

/-- The critical points of the Belyi polynomial are `0`, `1` and `(a+1)/(a+b+2)`. -/
