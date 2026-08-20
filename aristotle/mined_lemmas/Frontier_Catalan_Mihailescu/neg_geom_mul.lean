import Mathlib

/-!
# Catalan Mihailescu
Category: Frontier — Prime Numbers
Target: Frontier.Catalan_Mihailescu
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- The full Catalan–Mihăilescu theorem, as a statement (it is *not* proved in this file):
the only pair of consecutive perfect powers is `8 = 2 ^ 3` and `9 = 3 ^ 2`. -/

lemma neg_geom_mul (Y : ℤ) {q : ℕ} (hq : Odd q) :
    (∑ i ∈ Finset.range q, (-Y) ^ i) * (Y + 1) = Y ^ q + 1 := by
  have h := geom_sum_mul (-Y) q
  rw [hq.neg_pow] at h
  linarith [h]

/-- A positive integer divisor of `r ^ m` (`r` prime) is a power of `r`. -/
