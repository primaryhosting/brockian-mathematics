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

lemma not_congr_of_not_prime {n : ℕ} (hn : 2 ≤ n) (hnp : ¬ n.Prime) :
    ((X + 1 : (ZMod n)[X]))^n ≠ X^n + 1 := by
  intro heq
  set q := n.minFac with hqdef
  have hq : q.Prime := Nat.minFac_prime (by omega)
  have hqn : q ∣ n := Nat.minFac_dvd n
  have hlt : q < n := by
    rcases lt_or_eq_of_le (Nat.minFac_le (by omega : 0 < n)) with h | h
    · exact h
    · exact absurd (h ▸ hq) hnp
  -- compare coefficients of `X ^ q`
  have hcoeff := congrArg (fun p => Polynomial.coeff p q) heq
  simp only [Polynomial.coeff_X_add_one_pow, Polynomial.coeff_add, Polynomial.coeff_X_pow,
    Polynomial.coeff_one, if_neg (by omega : ¬ q = n), if_neg (by have := hq.two_le; omega : ¬ q = 0)]
    at hcoeff
  have hdvd : n ∣ n.choose q := (ZMod.natCast_eq_zero_iff _ _).mp (by simpa using hcoeff)
  have hc0 : n.choose q ≠ 0 := (Nat.choose_pos (le_of_lt hlt)).ne'
  have hfc := factorization_choose_of_prime_dvd hq hqn hlt
  have hpow : q ^ (n.factorization q) ∣ n.choose q :=
    dvd_trans (Nat.ordProj_dvd n q) hdvd
  have := (Nat.Prime.pow_dvd_iff_le_factorization hq hc0).mp hpow
  omega

/-- **AKS criterion (Agrawal–Kayal–Saxena).**  For `n ≥ 2`, the number `n` is prime if and
only if the polynomial identity `(X + a)^n = X^n + a^n` holds in `(ZMod n)[X]` for every
`a` coprime to `n`.

This is the algebraic characterization of primality on which the AKS deterministic
polynomial-time primality test ("PRIMES is in P") is based.  Note that what is formalized
here is this mathematical criterion, not the complexity-theoretic assertion about a machine
model (Mathlib provides no time-complexity framework in which the latter could be stated). -/
