import Mathlib
namespace Brockian.TwoSquaresUnique

/-- If `p` is prime and `p = a^2 + b^2`, then `a > 0`. -/

private lemma eq_of_mul_eq_mul_coprime {a b c d : ℕ} (hab : Nat.Coprime a b)
    (hcd : Nat.Coprime c d) (hc : 0 < c) (h : a * d = b * c) :
    a = c ∧ b = d := by
  have hac : a ∣ c := by
    have : a ∣ b * c := h.symm ▸ dvd_mul_right a d
    exact hab.dvd_of_dvd_mul_left this
  have hca : c ∣ a := by
    have : c ∣ a * d := h.symm ▸ dvd_mul_left c b
    exact hcd.dvd_of_dvd_mul_right this
  have eq1 : a = c := Nat.dvd_antisymm hac hca
  have eq2 : b = d := by
    have : b * c = d * c := by rw [eq1] at h; ring_nf; exact h.symm
    exact Nat.eq_of_mul_eq_mul_right hc this
  exact ⟨eq1, eq2⟩

/-- Brahmagupta–Fibonacci identity, first form. -/
