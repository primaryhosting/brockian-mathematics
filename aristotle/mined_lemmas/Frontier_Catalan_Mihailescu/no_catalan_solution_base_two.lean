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

theorem no_catalan_solution_base_two (p y q : ℕ) : ¬ IsCatalanSolution 2 p y q := by
  rintro ⟨-, hp, hy, hq, heq⟩
  -- `y` is odd, hence `y ≥ 3`
  have h2p : (2 : ℕ) ∣ 2 ^ p := dvd_pow_self 2 (by omega)
  have hyodd : ¬ (2 ∣ y) := by
    intro hdvd
    have : (2 : ℕ) ∣ y ^ q := dvd_pow hdvd (by omega)
    omega
  have hy3 : 3 ≤ y := by omega
  rcases Nat.even_or_odd q with hqe | hqo
  · -- even exponent: `2 ^ p = z ^ 2 + 1` with `z` odd, impossible mod `4`
    obtain ⟨t, ht⟩ := hqe
    have ht1 : 1 ≤ t := by omega
    have hz : y ^ q = (y ^ t) ^ 2 := by
      rw [← pow_mul]
      congr 1
      omega
    set z := y ^ t with hzdef
    have hzodd : ¬ (2 ∣ z) := by
      intro hdvd
      exact hyodd (Nat.Prime.dvd_of_dvd_pow Nat.prime_two hdvd)
    obtain ⟨s, hs⟩ : ∃ s, z = 2 * s + 1 := ⟨z / 2, by omega⟩
    have h4 : (4 : ℕ) ∣ 2 ^ p := by
      have : (2 : ℕ) ^ 2 ∣ 2 ^ p := pow_dvd_pow 2 (by omega)
      simpa using this
    have hzz : z ^ 2 = 4 * (s * s + s) + 1 := by rw [hs]; ring
    rw [hz, hzz] at heq
    omega
  · -- odd exponent
    have hq3 : 3 ≤ q := by
      rcases hqo with ⟨t, ht⟩; omega
    exact odd_pow_add_one_ne_two_pow hy3 hq3 hqo heq.symm

/-- The only solution of Catalan's equation with `y = 2` is `3 ^ 2 = 2 ^ 3 + 1`. -/
