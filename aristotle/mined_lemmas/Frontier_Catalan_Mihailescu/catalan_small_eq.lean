import Mathlib

/-!
# Catalan Mihailescu
Category: Frontier — Prime Numbers
Target: Frontier.Catalan_Mihailescu
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- The full Catalan–Mihăilescu theorem, as a statement (it is *not* proved in this file):
the only pair of consecutive perfect powers is `8 = 2 ^ 3` and `9 = 3 ^ 2`. -/

lemma catalan_small_eq {z r : ℕ} (hz : 2 ≤ z) (hr : 3 ≤ r) (h : z ^ r + 1 = r * (z + 1)) :
    r = 3 ∧ z = 2 := by
  have hr5 : r < 5 := by
    by_contra hc
    push_neg at hc
    have h1 : z * 2 ^ (r - 1) ≤ z ^ r := by
      have hpow : 2 ^ (r - 1) ≤ z ^ (r - 1) := Nat.pow_le_pow_left hz _
      calc z * 2 ^ (r - 1) ≤ z * z ^ (r - 1) := Nat.mul_le_mul_left _ hpow
      _ = z ^ r := by rw [← pow_succ']; congr 1; omega
    have h2 : 2 ^ (r - 1) = 2 * 2 ^ (r - 2) := by
      rw [show r - 1 = (r - 2) + 1 by omega, pow_succ]; ring
    have h3 : r < 2 ^ (r - 2) := lt_two_pow_sub hc
    nlinarith [h1, h2, h3, h]
  have hr34 : r = 3 ∨ r = 4 := by omega
  have hz2 : z = 2 := by
    by_contra hc
    have hz3 : 3 ≤ z := by omega
    have h9 : 9 * z ≤ z ^ 3 := by
      have hcube : z ^ 3 = z * z * z := by ring
      nlinarith [hz3]
    have h34 : z ^ 3 ≤ z ^ r := Nat.pow_le_pow_right (by omega) (by omega)
    rcases hr34 with rfl | rfl <;> omega
  subst hz2
  rcases hr34 with rfl | rfl
  · exact ⟨rfl, rfl⟩
  · exfalso; norm_num at h

/-- First stage for the larger base: if `r ^ m = y ^ q + 1` with `r` an odd prime and `q` odd,
then `r` divides `q`. -/
