import Mathlib
namespace Brockian.MsWilsonPrimePower

open Finset

/-- If an odd prime power `p ^ k` divides `(a - 1) * (a + 1)`, then it divides one of the two
factors, since `p` cannot divide both `a - 1` and `a + 1`. -/

private lemma prime_pow_dvd_of_dvd_pred_mul_succ (p k : ℕ) (hp : p.Prime) (hodd : Odd p) (a : ℤ)
    (h : ((p : ℤ) ^ k) ∣ (a - 1) * (a + 1)) :
    ((p : ℤ) ^ k) ∣ (a - 1) ∨ ((p : ℤ) ^ k) ∣ (a + 1) := by
  have hpi : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  by_cases hd : (p : ℤ) ∣ (a + 1)
  · right
    have hnd : ¬ (p : ℤ) ∣ (a - 1) := by
      intro h1
      have h2 : (p : ℤ) ∣ 2 := by simpa using dvd_sub hd h1
      have hp2 : p ∣ 2 := by exact_mod_cast h2
      have hpe : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2
      rw [hpe] at hodd
      simp [Nat.odd_iff] at hodd
    have hcop : IsCoprime ((p : ℤ) ^ k) (a - 1) :=
      IsCoprime.pow_left ((hpi.coprime_iff_not_dvd).mpr hnd)
    have h' : ((p : ℤ) ^ k) ∣ (a + 1) * (a - 1) := by rw [mul_comm]; exact h
    exact hcop.dvd_of_dvd_mul_right h'
  · left
    have hcop : IsCoprime ((p : ℤ) ^ k) (a + 1) :=
      IsCoprime.pow_left ((hpi.coprime_iff_not_dvd).mpr hd)
    exact hcop.dvd_of_dvd_mul_right h

/-- For an odd prime `p`, the only square roots of `1` in `ZMod (p ^ k)` are `±1`. -/
