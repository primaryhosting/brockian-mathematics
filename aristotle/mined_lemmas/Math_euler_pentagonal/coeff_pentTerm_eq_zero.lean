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

lemma coeff_pentTerm_eq_zero {n k : ℕ} (hk : n ≤ k) :
    (PowerSeries.coeff n) (((-1 : ℤ⟦X⟧)) ^ (k + 1) *
      (X ^ ((k + 1) * (3 * k + 2) / 2) + X ^ ((k + 1) * (3 * k + 4) / 2))) = 0 := by
  have h1 := le_pent1 k
  have h2 := le_pent2 k
  rw [coeff_pentTerm, if_neg (by omega), if_neg (by omega), add_zero]

