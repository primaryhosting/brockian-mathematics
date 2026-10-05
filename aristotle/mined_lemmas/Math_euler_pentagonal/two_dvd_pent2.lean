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

lemma two_dvd_pent2 (k : ℕ) : 2 ∣ (k + 1) * (3 * k + 4) := by
  rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · exact ⟨(m + m + 1) * (3 * m + 2), by ring⟩
  · exact ⟨(m + 1) * (6 * m + 7), by ring⟩

