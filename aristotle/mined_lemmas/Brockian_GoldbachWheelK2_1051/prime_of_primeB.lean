import Mathlib

/-!
# Goldbach Wheel K 2 1051
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1051
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace Brockian

/-- Trial division helper: `noFactorFrom f d n` is `true` when none of
`d, d+1, …` (up to `f` steps, stopping as soon as the divisor squared exceeds `n`)
divides `n`. -/

theorem prime_of_primeB {n : ℕ} (h : primeB n = true) : Nat.Prime n := by
  rw [primeB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h2, hnf⟩ := h
  by_contra hp
  have hpos : 0 < n := by omega
  have hle := Nat.minFac_sq_le_self hpos hp
  have hdvd := Nat.minFac_dvd n
  have h2m : 2 ≤ n.minFac := (Nat.minFac_prime (by omega)).two_le
  have hmn : n.minFac ≤ n := Nat.minFac_le hpos
  exact noFactorFrom_spec n 2 n hnf n.minFac h2m (by omega)
    (by nlinarith [sq_nonneg n.minFac, hle]) hdvd

/-- A number whose residue mod `6` is `1` or `5` is coprime to the `K = 2` wheel
modulus `6 = 2 * 3`. -/
