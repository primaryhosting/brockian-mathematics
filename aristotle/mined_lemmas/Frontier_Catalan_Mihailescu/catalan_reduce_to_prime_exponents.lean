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

theorem catalan_reduce_to_prime_exponents {x p y q : ℕ} (h : IsCatalanSolution x p y q) :
    ∃ X P Y Q : ℕ, IsCatalanSolution X P Y Q ∧ P.Prime ∧ Q.Prime ∧ x ≤ X ∧ y ≤ Y := by
  obtain ⟨hx, hp, hy, hq, heq⟩ := h
  have hpp : (Nat.minFac p).Prime := Nat.minFac_prime (by omega)
  have hqp : (Nat.minFac q).Prime := Nat.minFac_prime (by omega)
  have hdp : Nat.minFac p ∣ p := Nat.minFac_dvd p
  have hdq : Nat.minFac q ∣ q := Nat.minFac_dvd q
  have hp1 : 1 ≤ p / Nat.minFac p := Nat.one_le_div_iff (hpp.pos) |>.2 (Nat.minFac_le (by omega))
  have hq1 : 1 ≤ q / Nat.minFac q := Nat.one_le_div_iff (hqp.pos) |>.2 (Nat.minFac_le (by omega))
  refine ⟨x ^ (p / Nat.minFac p), Nat.minFac p, y ^ (q / Nat.minFac q), Nat.minFac q,
    ⟨?_, hpp.two_le, ?_, hqp.two_le, ?_⟩, hpp, hqp, ?_, ?_⟩
  · calc 2 ≤ x := hx
      _ = x ^ 1 := (pow_one x).symm
      _ ≤ x ^ (p / Nat.minFac p) := Nat.pow_le_pow_right (by omega) hp1
  · calc 2 ≤ y := hy
      _ = y ^ 1 := (pow_one y).symm
      _ ≤ y ^ (q / Nat.minFac q) := Nat.pow_le_pow_right (by omega) hq1
  · rw [← pow_mul, ← pow_mul, Nat.div_mul_cancel hdp, Nat.div_mul_cancel hdq]
    exact heq
  · calc x = x ^ 1 := (pow_one x).symm
      _ ≤ x ^ (p / Nat.minFac p) := Nat.pow_le_pow_right (by omega) hp1
  · calc y = y ^ 1 := (pow_one y).symm
      _ ≤ y ^ (q / Nat.minFac q) := Nat.pow_le_pow_right (by omega) hq1

/-- A Lean-checked reduction of the Catalan–Mihăilescu theorem: it suffices to rule out
solutions with prime exponents and both bases at least `3`. -/
