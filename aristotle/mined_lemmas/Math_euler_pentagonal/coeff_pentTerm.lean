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

lemma coeff_pentTerm (n k : ℕ) :
    (PowerSeries.coeff n) (((-1 : ℤ⟦X⟧)) ^ (k + 1) *
        (X ^ ((k + 1) * (3 * k + 2) / 2) + X ^ ((k + 1) * (3 * k + 4) / 2)))
      = (if (k + 1) * (3 * k + 2) / 2 = n then ((-1 : ℤ)) ^ (k + 1) else 0)
        + (if (k + 1) * (3 * k + 4) / 2 = n then ((-1 : ℤ)) ^ (k + 1) else 0) := by
  rw [mul_add, map_add, coeff_sign_X_pow, coeff_sign_X_pow]

