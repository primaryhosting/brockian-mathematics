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

lemma pent2_iff (k n : ℕ) : (k + 1) * (3 * k + 4) / 2 = n ↔ 2 * n = (k + 1) * (3 * (k + 1) + 1) := by
  obtain ⟨q, hq⟩ := two_dvd_pent2 k
  have e : 3 * (k + 1) + 1 = 3 * k + 4 := by omega
  rw [e, hq]
  omega

