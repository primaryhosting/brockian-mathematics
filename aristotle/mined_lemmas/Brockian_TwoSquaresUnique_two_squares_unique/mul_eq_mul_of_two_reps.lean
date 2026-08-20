import Mathlib
namespace Brockian.TwoSquaresUnique

/-- If `p` is prime and `p = a^2 + b^2`, then `a > 0`. -/

private lemma mul_eq_mul_of_two_reps {p a b c d : ℕ} (hp : p.Prime)
    (hab : p = a ^ 2 + b ^ 2) (hcd : p = c ^ 2 + d ^ 2) :
    a * d = b * c ∨ a * c = b * d := by
  have hdiv : (p : ℤ) ∣ ((a : ℤ) * d - b * c) * ((a : ℤ) * d + b * c) := dvd_mul_cross hab hcd
  have hprime : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr hp
  have ha : 0 < a := pos_of_prime_sq_add_sq hp hab
  have hb : 0 < b := pos_of_prime_sq_add_sq hp (by rw [hab, add_comm] : p = b ^ 2 + a ^ 2)
  have hc : 0 < c := pos_of_prime_sq_add_sq hp hcd
  have hd : 0 < d := pos_of_prime_sq_add_sq hp (by rw [hcd, add_comm] : p = d ^ 2 + c ^ 2)
  have hab' : ((p : ℤ)) = (a : ℤ) ^ 2 + (b : ℤ) ^ 2 := by exact_mod_cast hab
  have hcd' : ((p : ℤ)) = (c : ℤ) ^ 2 + (d : ℤ) ^ 2 := by exact_mod_cast hcd
  have hp2 : ((p : ℤ) ^ 2) = ((a : ℤ) * c + b * d) ^ 2 + ((a : ℤ) * d - b * c) ^ 2 := by
    have := brahmagupta_one a b c d
    simp only [← hab', ← hcd'] at this ⊢
    linarith
  have hp2' : ((p : ℤ) ^ 2) = ((a : ℤ) * c - b * d) ^ 2 + ((a : ℤ) * d + b * c) ^ 2 := by
    have := brahmagupta_two a b c d
    simp only [← hab', ← hcd'] at this ⊢
    linarith
  rcases hprime.dvd_or_dvd hdiv with hdvd1 | hdvd2
  · -- Case: p ∣ (ad - bc)
    rcases int_sq_split hp2 hdvd1 with heq | heq
    · left; exact_mod_cast (sub_eq_zero.mp heq)
    · nlinarith [show (a : ℤ) > 0 from mod_cast ha, show (b : ℤ) > 0 from mod_cast hb,
        show (c : ℤ) > 0 from mod_cast hc, show (d : ℤ) > 0 from mod_cast hd]
  · -- Case: p ∣ (ad + bc)
    rcases int_sq_split hp2' hdvd2 with heq | heq
    · nlinarith [show (a : ℤ) > 0 from mod_cast ha, show (b : ℤ) > 0 from mod_cast hb,
        show (c : ℤ) > 0 from mod_cast hc, show (d : ℤ) > 0 from mod_cast hd]
    · right; exact_mod_cast (sub_eq_zero.mp heq)

/-- Uniqueness in Fermat's two-square theorem: a prime p ≡ 1 (mod 4) has an essentially unique
    representation as a sum of two squares (ordered a ≤ b).

    (The hypothesis `hp1 : p % 4 = 1` is not needed for uniqueness; it is kept as it is part of
    the requested statement.) -/
