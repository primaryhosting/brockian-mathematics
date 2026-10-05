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

lemma pent_cross {a b : ℕ} (ha : 1 ≤ a) (h : a * (3 * a - 1) = b * (3 * b + 1)) : False := by
  have e1 := pent1_key a ha
  have hb2 : b * (3 * b + 1) = 3 * b * b + b := by ring
  have key : 3 * a * a = 3 * b * b + b + a := by linarith
  have key' : 3 * (a : ℤ) * a = 3 * (b : ℤ) * b + b + a := by exact_mod_cast key
  have hfac : ((a : ℤ) + b) * (3 * ((a : ℤ) - b) - 1) = 0 := by ring_nf; linarith
  rcases mul_eq_zero.1 hfac with h1 | h1
  · omega
  · omega

