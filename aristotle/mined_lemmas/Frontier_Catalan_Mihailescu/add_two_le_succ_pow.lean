import Mathlib
/-!
# Catalan Mihailescu
Category: Frontier — Prime Numbers
Target: Frontier.Catalan_Mihailescu
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000

namespace Frontier

/-- A *Catalan solution*: a pair of consecutive perfect powers, i.e. natural numbers with
`x ^ p = y ^ q + 1`, all of `x, y, p, q` being at least `2`. -/

lemma add_two_le_succ_pow {b n : ℕ} (hb : 1 ≤ b) (hn : 2 ≤ n) : b ^ n + 2 ≤ (b + 1) ^ n := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n
      · omega
      · have h1 : (b + 1) ^ (1 + 1) = b ^ (1 + 1) + 2 * b + 1 := by ring
        omega
    · have hih := ih h
      have hexp : (b + 1) ^ (n + 1) = (b + 1) * (b + 1) ^ n := by ring
      have hb' : b ^ (n + 1) = b * b ^ n := by ring
      nlinarith [pow_pos (show 0 < b by omega) n]

/-- Two `n`-th powers of positive numbers with `n ≥ 2` never differ by exactly `1`. -/
