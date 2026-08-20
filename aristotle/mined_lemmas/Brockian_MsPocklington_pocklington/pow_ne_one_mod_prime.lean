import Mathlib
namespace Brockian.MsPocklington

/-- If `p` is a prime divisor of `N` and `gcd (a ^ m - 1) N = 1`, then `a ^ m ≢ 1 (mod p)`. -/

private lemma pow_ne_one_mod_prime {N a m p : ℕ} (h2 : Nat.gcd (a ^ m - 1) N = 1)
    (hp : p.Prime) (hpN : p ∣ N) : ¬ (a ^ m ≡ 1 [MOD p]) := by
  intro h
  have hdiv : p ∣ a ^ m - 1 := by
    by_cases ham : a ^ m ≥ 1
    · rw [Nat.modEq_iff_dvd] at h
      have hpz : (p : ℤ) ∣ ↑(a ^ m) - 1 := by
        have := h.neg_right
        simpa using this
      exact_mod_cast hpz
    · -- `a ^ m < 1` means `a ^ m = 0`
      have ham0 : a ^ m = 0 := Nat.lt_one_iff.mp (Nat.not_le.mp ham)
      rw [ham0] at h
      rcases p with _ | _ | p <;> simp_all
  have hgcd := Nat.dvd_gcd hdiv hpN
  rw [h2] at hgcd
  exact Nat.Prime.not_dvd_one hp hgcd

/-- If `d ∣ q * m` with `q` prime and `d ∤ m`, then `q ∣ d`. -/
