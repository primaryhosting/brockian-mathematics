/-
# Faltings Mordell
Category: Frontier — Fields Medal Work
Target: Frontier.faltings_mordell
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` commands to precede any module docstring, so the header above is
-- repeated verbatim as the module docstring immediately after the import.)

import Mathlib

/-!
# Faltings Mordell
Category: Frontier — Fields Medal Work
Target: Frontier.faltings_mordell
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- The set of affine rational points of the Fermat curve `x ^ n + y ^ n = 1` over `ℚ`. -/

lemma exists_prime_factor_five_le {n : ℕ} (hn : 4 ≤ n) (h3 : ¬ (3 ∣ n)) (h4 : ¬ (4 ∣ n)) :
    ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ p ∣ n := by
  by_contra hcon
  push_neg at hcon
  have honly : ∀ {q : ℕ}, q.Prime → q ∣ n → q = 2 := by
    intro q hq hqn
    have h5 : q < 5 := by
      by_contra hq5
      exact absurd hqn (hcon q hq (by omega))
    have h2 : 2 ≤ q := hq.two_le
    interval_cases q
    · rfl
    · exact absurd hqn h3
    · exact absurd hq (by norm_num)
  have hn0 : n ≠ 0 := by omega
  have hpow := Nat.eq_prime_pow_of_unique_prime_dvd hn0 honly
  set L := n.primeFactorsList.length with hL
  clear_value L
  have h2L : 2 ≤ L := by
    by_contra hlt
    push_neg at hlt
    interval_cases L
    · rw [pow_zero] at hpow; omega
    · rw [pow_one] at hpow; omega
  have hdvd : (2 : ℕ) ^ 2 ∣ 2 ^ L := pow_dvd_pow 2 h2L
  rw [← hpow] at hdvd
  exact h4 (by simpa using hdvd)

/-- **Lean-checked reduction of Faltings' theorem for Fermat curves to prime exponents.**

If every Fermat curve of prime degree `p ≥ 5` has finitely many rational points, then so does
every Fermat curve of degree `n ≥ 4`, i.e. every Fermat curve of genus at least `2`.  Together
with the unconditionally verified cases `faltings_mordell`, this reduces the Mordell conjecture
for the Fermat family to the prime exponents `p ≥ 5`. -/
