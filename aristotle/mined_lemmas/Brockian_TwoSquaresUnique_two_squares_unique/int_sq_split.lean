import Mathlib
namespace Brockian.TwoSquaresUnique

/-- If `p` is prime and `p = a^2 + b^2`, then `a > 0`. -/

private lemma int_sq_split {P X Y : ℤ} (h : P ^ 2 = X ^ 2 + Y ^ 2) (hdvd : P ∣ Y) :
    Y = 0 ∨ X = 0 := by
  obtain ⟨k, hk⟩ := hdvd
  rw [hk] at h
  have h'' : P ^ 2 * (1 - k ^ 2) = X ^ 2 := by nlinarith [sq_nonneg X]
  by_cases hk0 : k = 0
  · left; simp [hk0, hk]
  · right
    have hk1 : k ≤ -1 ∨ 1 ≤ k := by omega
    have hk2 : k ^ 2 ≥ 1 := by rcases hk1 with hk1 | hk1 <;> nlinarith
    have : P ^ 2 * (1 - k ^ 2) ≤ 0 := by nlinarith
    nlinarith [sq_nonneg X]

/-- Cross-multiplication cancellation for two coprime pairs. -/
