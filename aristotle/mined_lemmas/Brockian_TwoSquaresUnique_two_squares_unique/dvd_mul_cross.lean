import Mathlib
namespace Brockian.TwoSquaresUnique

/-- If `p` is prime and `p = a^2 + b^2`, then `a > 0`. -/

private lemma dvd_mul_cross {p a b c d : ℕ} (hab : p = a ^ 2 + b ^ 2) (hcd : p = c ^ 2 + d ^ 2) :
    (p : ℤ) ∣ ((a : ℤ) * d - b * c) * ((a : ℤ) * d + b * c) := by
  have heq : (a : ℤ) ^ 2 + b ^ 2 = c ^ 2 + d ^ 2 := by
    norm_cast
    linarith
  have h : ((a : ℤ) * d - b * c) * ((a : ℤ) * d + b * c) = (p : ℤ) * (p - c ^ 2 - b ^ 2) := by
    have hc2 : (c : ℤ) ^ 2 = (a : ℤ) ^ 2 + b ^ 2 - d ^ 2 := by linarith
    push_cast [hab]
    ring_nf
    rw [hc2]
    ring
  rw [h]
  exact dvd_mul_right _ _

/-- Two representations of a prime as a sum of two squares satisfy one of the two
Brahmagupta degeneracies. -/
