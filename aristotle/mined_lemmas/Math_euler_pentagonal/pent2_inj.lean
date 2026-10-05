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

lemma pent2_inj {a b : ℕ} (h : a * (3 * a + 1) = b * (3 * b + 1)) : a = b := by
  rcases lt_trichotomy a b with hlt | heq | hlt
  · nlinarith
  · exact heq
  · nlinarith

