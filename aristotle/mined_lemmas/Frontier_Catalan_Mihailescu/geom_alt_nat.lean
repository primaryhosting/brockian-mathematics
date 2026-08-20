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

lemma geom_alt_nat (w m : ℕ) :
    ((∑ k ∈ Finset.range m, (w + 1) ^ (2 * k + 1) * w) + 1) * (w + 2)
      = (w + 1) ^ (2 * m + 1) + 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ]
      ring_nf
      ring_nf at ih
      nlinarith [ih]

/-- Binomial expansion modulo `d ^ 2`: `(1 + d) ^ i = 1 + i * d + M * d ^ 2`. -/
