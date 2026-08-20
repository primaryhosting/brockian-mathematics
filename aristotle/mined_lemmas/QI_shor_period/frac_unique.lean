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

lemma frac_unique {N Q c : ℕ} {r r' s s' : ℕ} (hr : 0 < r) (hr' : 0 < r')
    (hrN : r ≤ N) (hr'N : r' ≤ N) (hQ : ((N : ℝ)) ^ 2 ≤ Q) (hQ0 : 0 < Q)
    (h1 : |(c : ℝ) / Q - (s : ℝ) / r| < 1 / (2 * Q))
    (h2 : |(c : ℝ) / Q - (s' : ℝ) / r'| < 1 / (2 * Q)) :
    (s : ℝ) / r = (s' : ℝ) / r' := by
  by_contra hne
  have hQ0' : (0 : ℝ) < Q := by exact_mod_cast hQ0
  have hrr : ((r : ℝ) * r') ≤ (N : ℝ) ^ 2 := by
    have h1' : (r : ℝ) ≤ N := by exact_mod_cast hrN
    have h2' : (r' : ℝ) ≤ N := by exact_mod_cast hr'N
    have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
    have hr0' : (0 : ℝ) < r' := by exact_mod_cast hr'
    nlinarith
  have hlow := abs_sub_div_ge hr hr' hne
  have hhigh : |(s : ℝ) / r - (s' : ℝ) / r'| < 1 / Q := by
    have hsum : |(s : ℝ) / r - (s' : ℝ) / r'| ≤
        |(s : ℝ) / r - (c : ℝ) / Q| + |(c : ℝ) / Q - (s' : ℝ) / r'| :=
      abs_sub_le _ _ _
    have hswap : |(s : ℝ) / r - (c : ℝ) / Q| = |(c : ℝ) / Q - (s : ℝ) / r| := abs_sub_comm _ _
    have heq : 1 / (2 * (Q : ℝ)) + 1 / (2 * Q) = 1 / Q := by field_simp; ring
    rw [hswap] at hsum
    linarith
  have hrr0 : (0 : ℝ) < (r : ℝ) * r' := by
    have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
    have hr0' : (0 : ℝ) < r' := by exact_mod_cast hr'
    positivity
  have : 1 / (Q : ℝ) ≤ 1 / ((r : ℝ) * r') := by
    apply one_div_le_one_div_of_le hrr0
    linarith
  linarith

/-- **Coprime fractions with the same value have the same denominator.** -/
