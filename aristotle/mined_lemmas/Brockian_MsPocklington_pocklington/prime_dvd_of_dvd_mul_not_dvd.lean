import Mathlib
namespace Brockian.MsPocklington

/-- If `p` is a prime divisor of `N` and `gcd (a ^ m - 1) N = 1`, then `a ^ m ≢ 1 (mod p)`. -/

private lemma prime_dvd_of_dvd_mul_not_dvd {q m d : ℕ} (hq : q.Prime) (hdvd : d ∣ q * m)
    (hnd : ¬ d ∣ m) : q ∣ d := by
  by_contra hqnd
  have hcoprime : Nat.Coprime d q := (hq.coprime_iff_not_dvd.mpr hqnd).symm
  exact hnd (hcoprime.dvd_of_dvd_mul_left hdvd)

/-- Key step: every prime divisor `p` of `N` satisfies `q ∣ p - 1`. -/
