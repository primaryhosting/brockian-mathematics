import Mathlib

/-!
# Is Betrothed Pair Iff Nontrivial Two Cycle
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.Dynamics.isBetrothedPair_iff_nontrivial_twoCycle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Nat

set_option autoImplicit false

namespace Brockian.BetrothedNumbers

/-- The sum-of-divisors function `σ₁(n) = ∑_{d ∣ n} d`, i.e. `ArithmeticFunction.sigma 1`. -/
noncomputable def sigmaOne (n : ℕ) : ℕ := ArithmeticFunction.sigma 1 n

lemma sigmaOne_eq_sum (n : ℕ) : sigmaOne n = ∑ d ∈ n.divisors, d := by
  simp [sigmaOne, ArithmeticFunction.sigma_one_apply]

/-- The *betrothed partner* map: `partner n = σ₁(n) - n - 1`, i.e. the sum of the
divisors of `n` other than `1` and `n` itself. -/
noncomputable def partner (n : ℕ) : ℕ := sigmaOne n - n - 1

/-- `m` and `n` form a *betrothed (quasi-amicable) pair* if they are distinct positive
integers with `σ₁(m) = σ₁(n) = m + n + 1`. -/
def IsBetrothedPair (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ m ≠ n ∧ sigmaOne m = m + n + 1 ∧ sigmaOne n = m + n + 1

namespace Dynamics

/-- For a positive `n`, `n` itself is a divisor of `n`, so `n ≤ σ₁(n)`. -/
lemma le_sigmaOne {n : ℕ} (hn : 0 < n) : n ≤ sigmaOne n := by
  rw [sigmaOne_eq_sum]
  exact Finset.single_le_sum (f := fun d => d) (fun _ _ => Nat.zero_le _)
    (Nat.mem_divisors_self n hn.ne')

/-- If `partner m = n` with `m` and `n` positive, then no truncation occurred in the
natural subtraction, i.e. `σ₁(m) = m + n + 1`. -/
lemma sigmaOne_eq_of_partner_eq {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (h : partner m = n) : sigmaOne m = m + n + 1 := by
  have hle : m ≤ sigmaOne m := le_sigmaOne hm
  rw [partner] at h
  omega

/--
**Characterization of betrothed pairs as nontrivial positive 2-cycles.**

`(m, n)` is a betrothed pair exactly when `m` and `n` are positive, distinct, and form a
2-cycle of the partner map `partner n = σ₁(n) - n - 1`.
-/
theorem isBetrothedPair_iff_nontrivial_twoCycle (m n : ℕ) :
    IsBetrothedPair m n ↔
      0 < m ∧ 0 < n ∧ m ≠ n ∧ partner m = n ∧ partner n = m := by
  constructor
  · rintro ⟨hm, hn, hmn, hsm, hsn⟩
    refine ⟨hm, hn, hmn, ?_, ?_⟩ <;> rw [partner] <;> omega
  · rintro ⟨hm, hn, hmn, hpm, hpn⟩
    have h1 : sigmaOne m = m + n + 1 := sigmaOne_eq_of_partner_eq hm hn hpm
    have h2 : sigmaOne n = n + m + 1 := sigmaOne_eq_of_partner_eq hn hm hpn
    exact ⟨hm, hn, hmn, h1, by omega⟩

/-- Sanity check that the characterization is not vacuous: `(48, 75)` is the smallest
betrothed pair, and hence a nontrivial positive 2-cycle of `partner`. -/
example : partner 48 = 75 ∧ partner 75 = 48 ∧ (48 : ℕ) ≠ 75 := by
  have h := (isBetrothedPair_iff_nontrivial_twoCycle 48 75).mp
    ⟨by norm_num, by norm_num, by norm_num, by simp [sigmaOne]; decide, by
      simp [sigmaOne]; decide⟩
  exact ⟨h.2.2.2.1, h.2.2.2.2, h.2.2.1⟩

end Dynamics

end Brockian.BetrothedNumbers

