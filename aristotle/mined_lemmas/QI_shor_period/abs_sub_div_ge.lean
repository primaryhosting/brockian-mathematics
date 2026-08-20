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

lemma abs_sub_div_ge {r r' : ℕ} (hr : 0 < r) (hr' : 0 < r') {s s' : ℕ}
    (hne : (s : ℝ) / r ≠ (s' : ℝ) / r') :
    1 / ((r : ℝ) * r') ≤ |(s : ℝ) / r - (s' : ℝ) / r'| := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hr0' : (0 : ℝ) < r' := by exact_mod_cast hr'
  have hkey : (s : ℝ) / r - (s' : ℝ) / r' = ((s : ℝ) * r' - (s' : ℝ) * r) / ((r : ℝ) * r') := by
    field_simp
  have hZ : (s * r' : ℤ) - (s' * r : ℤ) ≠ 0 := by
    intro h
    apply hne
    have hR : (s : ℝ) * r' = (s' : ℝ) * r := by
      have := congrArg (fun z : ℤ => (z : ℝ)) h
      push_cast at this
      linarith
    field_simp
    linarith
  have h1 : (1 : ℝ) ≤ |(s : ℝ) * r' - (s' : ℝ) * r| := by
    have hint : (1 : ℤ) ≤ |(s * r' : ℤ) - (s' * r : ℤ)| := Int.one_le_abs (by simpa using hZ)
    have : ((1 : ℤ) : ℝ) ≤ ((|(s * r' : ℤ) - (s' * r : ℤ)| : ℤ) : ℝ) := by exact_mod_cast hint
    rw [Int.cast_abs] at this
    push_cast at this
    exact this
  rw [hkey, abs_div, abs_of_pos (by positivity : (0:ℝ) < (r : ℝ) * r')]
  rw [div_le_div_iff_of_pos_right (by positivity)]
  exact h1

/-- **Uniqueness of the fraction recovered from a measurement.**
If two fractions with denominators at most `N` both lie within `1/(2Q)` of `c/Q`,
where `Q ≥ N^2`, then they are equal. This is the classical post-processing step
of Shor's algorithm (continued-fraction expansion of `c/Q`). -/
