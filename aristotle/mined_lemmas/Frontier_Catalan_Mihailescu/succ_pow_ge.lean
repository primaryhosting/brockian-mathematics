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

lemma succ_pow_ge (b n : ℕ) (hb : 1 ≤ b) (hn : 2 ≤ n) :
    b ^ n + 2 * b + 1 ≤ (b + 1) ^ n := by
  induction n, hn using Nat.le_induction with
  | base => ring_nf; nlinarith
  | succ n hn ih =>
      have h1 : (b + 1) ^ (n + 1) = (b + 1) ^ n * (b + 1) := by ring
      have h2 : b ^ (n + 1) = b ^ n * b := by ring
      nlinarith [pow_pos (show 0 < b by omega) n]

/-- The geometric sum identity over `ℕ`, in the form `(∑ i < p, x ^ i) * (x - 1) + 1 = x ^ p`
with `x = c + 1`. -/
