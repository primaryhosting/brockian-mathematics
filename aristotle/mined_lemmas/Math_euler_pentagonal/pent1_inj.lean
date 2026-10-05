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

lemma pent1_inj {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (h : a * (3 * a - 1) = b * (3 * b - 1)) :
    a = b := by
  have e1 := pent1_key a ha
  have e2 := pent1_key b hb
  rcases lt_trichotomy a b with hlt | heq | hlt
  · nlinarith
  · exact heq
  · nlinarith

