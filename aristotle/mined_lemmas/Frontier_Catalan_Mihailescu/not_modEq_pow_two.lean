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

lemma not_modEq_pow_two {k n : ℕ} (hn : k + 1 ≤ n) : ¬ ((2 : ℕ) ^ n ≡ 2 ^ k [MOD 2 ^ (k + 1)]) := by
  intro h
  have hdvd : (2 : ℕ) ^ (k + 1) ∣ 2 ^ n := pow_dvd_pow 2 hn
  have h0 : 2 ^ n % 2 ^ (k + 1) = 0 := Nat.dvd_iff_mod_eq_zero.mp hdvd
  have hlt : (2 : ℕ) ^ k < 2 ^ (k + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have h1 : (2 : ℕ) ^ k % 2 ^ (k + 1) = 2 ^ k := Nat.mod_eq_of_lt hlt
  have hk : 0 < (2 : ℕ) ^ k := Nat.two_pow_pos k
  rw [Nat.ModEq, h0, h1] at h
  omega

/-- If `u ^ 2 ≡ 1` modulo `m`, then `u ^ e ≡ u` modulo `m` for every odd `e`. -/
