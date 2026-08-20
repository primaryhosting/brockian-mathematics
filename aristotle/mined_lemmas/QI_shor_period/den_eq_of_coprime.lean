/-
# Shor Period
Category: Frontier Qi
Target: QI.shor_period
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Shor Period
Category: Frontier Qi
Target: QI.shor_period
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QI

/-- **Two distinct fractions with small denominators are far apart.**
If `s/r ≠ s'/r'` then they differ by at least `1/(r*r')`. -/

lemma den_eq_of_coprime {r r' s s' : ℕ} (hr : 0 < r) (hr' : 0 < r')
    (hc : Nat.Coprime s r) (hc' : Nat.Coprime s' r')
    (h : (s : ℝ) / r = (s' : ℝ) / r') : r = r' := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hr0' : (0 : ℝ) < r' := by exact_mod_cast hr'
  have hmul : (s : ℝ) * r' = (s' : ℝ) * r := by
    field_simp at h
    linarith
  have hnat : s * r' = s' * r := by exact_mod_cast hmul
  have hdvd : r ∣ r' := by
    have : r ∣ s * r' := ⟨s', by rw [hnat]; ring⟩
    exact (Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.symm hc) this)
  have hdvd' : r' ∣ r := by
    have : r' ∣ s' * r := ⟨s, by rw [← hnat]; ring⟩
    exact (Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.symm hc') this)
  exact Nat.dvd_antisymm hdvd hdvd'

/-- **Shor's period finding.**

Let `a` be a unit modulo `N` and let `r = orderOf a` be the (multiplicative) order of `a`,
i.e. the period of the modular exponentiation function `x ↦ a ^ x mod N`.
Suppose the quantum phase-estimation register has size `Q ≥ N ^ 2`, and the measured
outcome `c` yields a good estimate of some phase `s / r` (with `s` coprime to `r`),
namely `|c/Q - s/r| < 1/(2Q)` — the event which occurs with high probability.

Then:
1. `r` is a period of the modular exponentiation function;
2. `r` is the *least* positive period;
3. the classical post-processing is unambiguous: *any* fraction `s'/r'` in lowest terms
   with denominator `r' ≤ N` that is compatible with the measurement `c` has `r' = r`,
   so the algorithm outputs exactly the period `r`.
-/
