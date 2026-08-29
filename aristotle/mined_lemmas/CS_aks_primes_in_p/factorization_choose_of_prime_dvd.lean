import Mathlib

/-!
# Aks Primes In P
Category: Frontier Cs
Target: CS.aks_primes_in_p
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Polynomial Finset

namespace CS

/-- For `q` a prime factor of `n` with `q < n`, the product `∏_{i=1}^{q-1} (n - i)`
is not divisible by `q`. -/

lemma factorization_choose_of_prime_dvd {n q : ℕ} (hq : q.Prime) (hqn : q ∣ n) (hlt : q < n) :
    (n.choose q).factorization q + 1 = n.factorization q := by
  have hn0 : n ≠ 0 := by omega
  have hq2 : 2 ≤ q := hq.two_le
  set M := ∏ i ∈ Finset.Ico 1 q, (n - i) with hM
  have hM0 : M ≠ 0 := by
    rw [hM, Finset.prod_ne_zero_iff]
    intro i hi
    simp only [Finset.mem_Ico] at hi
    omega
  have hqM : ¬ q ∣ M := not_dvd_prod_Ico hq hqn hlt
  have hdesc : n.descFactorial q = n * M := by
    rw [Nat.descFactorial_eq_prod_range, Finset.range_eq_Ico,
      Finset.prod_eq_prod_Ico_succ_bot hq.pos]
    simp [hM]
  have hkey : q.factorial * n.choose q = n * M := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose, hdesc]
  have hc0 : n.choose q ≠ 0 := (Nat.choose_pos (le_of_lt hlt)).ne'
  have hfac0 : q.factorial ≠ 0 := Nat.factorial_ne_zero q
  -- valuation of `q !` at `q` is one
  have hfacq : (q.factorial).factorization q = 1 := by
    obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
    rw [Nat.factorial_succ, Nat.factorization_mul (by omega) (Nat.factorial_ne_zero m)]
    have : ¬ (m + 1) ∣ m.factorial := by
      intro h
      have := (Nat.Prime.dvd_factorial hq).mp h
      omega
    simp [hq.factorization_self, Nat.factorization_eq_zero_of_not_dvd this]
  have h1 : (q.factorial * n.choose q).factorization q
      = 1 + (n.choose q).factorization q := by
    rw [Nat.factorization_mul hfac0 hc0]
    simp [hfacq]
  have h2 : (n * M).factorization q = n.factorization q := by
    rw [Nat.factorization_mul hn0 hM0]
    simp [Nat.factorization_eq_zero_of_not_dvd hqM]
  rw [hkey, h2] at h1
  omega

/-- If `n ≥ 2` is not prime, the polynomial congruence `(X+1)^n = X^n + 1` fails
in `(ZMod n)[X]`. -/
