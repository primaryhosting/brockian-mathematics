import Mathlib
namespace Brockian.MsProth

open Nat in
/-- If `d ∣ k * 2 ^ n` and `2 ^ n ∤ d`, then already `d ∣ k * 2 ^ (n - 1)`. -/

private lemma dvd_half_of_not_two_pow_dvd {k n d : ℕ} (hn : 1 ≤ n)
    (hd : d ∣ k * 2 ^ n) (h2 : ¬ (2 ^ n ∣ d)) : d ∣ k * 2 ^ (n - 1) := by
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact h2 (dvd_zero _)
  have hsn : d.factorization 2 < n := by
    by_contra h
    push_neg at h
    exact h2 (dvd_trans (pow_dvd_pow 2 h) (Nat.ordProj_dvd d 2))
  have hodd : Odd (ordCompl[2] d) :=
    Nat.odd_iff.mpr (Nat.not_even_iff.mp
      (fun he => Nat.not_dvd_ordCompl Nat.prime_two hd0 he.two_dvd))
  have hcop : Nat.Coprime (ordCompl[2] d) (2 ^ n) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hodd)
  have hm : ordCompl[2] d ∣ k := hcop.dvd_of_dvd_mul_right ((Nat.ordCompl_dvd d 2).trans hd)
  have hkey : d ∣ 2 ^ (n - 1) * k := by
    calc d = ordProj[2] d * ordCompl[2] d := (Nat.ordProj_mul_ordCompl_eq_self d 2).symm
      _ ∣ 2 ^ (n - 1) * k := mul_dvd_mul (pow_dvd_pow 2 (by omega)) hm
  simpa [mul_comm] using hkey

/-- Every prime factor `p` of a Proth number `N = k * 2 ^ n + 1` admitting a witness `a` with
`a ^ ((N-1)/2) = -1` satisfies `2 ^ n ∣ p - 1`. -/
