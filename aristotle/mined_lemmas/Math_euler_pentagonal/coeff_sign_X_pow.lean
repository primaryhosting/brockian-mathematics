import Mathlib

/-!
# Euler Pentagonal
Category: Pure Mathematics
Target: Math.euler_pentagonal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset PowerSeries
open scoped PowerSeries.WithPiTopology

namespace Math

/-! ## Distinct partitions as finsets of positive integers -/

/-- The finset of all "partitions of `n` into distinct parts", encoded as finsets of
positive integers whose sum is `n`. -/

lemma coeff_sign_X_pow (n k m : ℕ) :
    (PowerSeries.coeff (R := ℤ) n) (((-1 : ℤ⟦X⟧)) ^ k * X ^ m)
      = if m = n then ((-1 : ℤ)) ^ k else 0 := by
  rw [show ((-1 : ℤ⟦X⟧)) ^ k = C ((-1 : ℤ) ^ k) by rw [map_pow]; norm_num,
    PowerSeries.coeff_C_mul]
  rcases eq_or_ne m n with rfl | h
  · simp
  · rw [PowerSeries.coeff_X_pow, if_neg (Ne.symm h), if_neg h]; ring

