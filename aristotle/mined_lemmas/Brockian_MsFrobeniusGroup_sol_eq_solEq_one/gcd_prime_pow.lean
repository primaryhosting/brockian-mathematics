import Mathlib

/-!
# Frobenius's theorem

For a finite group `G` and any `n`, `gcd (n, |G|)` divides the number of solutions of `xⁿ = 1`.

The proof is organised as follows.

* `sol G n` is the number of solutions of `x ^ n = 1`, `solEq n y` the number of solutions of
  `x ^ n = y`.
* `solEq_prime_pow_dvd`: if `y` has order `p ^ k` with `k ≥ 1`, then `p ^ a` divides the number
  of solutions of `x ^ (p ^ a) = y`.  (Each solution generates a cyclic group of order `p ^ (a+k)`
  containing `y`, and each such cyclic subgroup contains exactly `p ^ a` solutions.)
* Consequently `sol G (p ^ (a+1)) ≡ sol G (p ^ a) [MOD p ^ a]`, so all the numbers
  `sol G (p ^ b)` for `b ≥ a` are congruent mod `p ^ a`.
* `sol_mul_eq_sum`: writing `n = p ^ α * u` with `p ∤ u`, decomposing an element into its
  `p`-part and `p'`-part gives `sol G n = ∑_{w ^ u = 1} sol (centralizer w) (p ^ α)`.
* `pPart_dvd_sol_pPart` (the key theorem): the number of `p`-elements of `G` is divisible by the
  order of a Sylow `p`-subgroup.  This follows by induction on `|G|` from the previous identity
  applied to `n = |G|`, grouping the sum into conjugacy classes.
* Everything is then assembled.
-/

namespace Brockian.MsFrobeniusGroup

open scoped Classical
open Finset

universe u

variable {G : Type u} [Group G]

/-- The number of solutions of `x ^ n = 1` in `G`. -/

lemma gcd_prime_pow {p : ℕ} (hp : p.Prime) (a N : ℕ) (hN : N ≠ 0) :
    Nat.gcd (p ^ a) N = p ^ (min a (N.factorization p)) := by
  have h1 : Nat.factorization (Nat.gcd (p ^ a) N) p = min (Nat.factorization (p ^ a) p) (Nat.factorization N p) := by
    have := Nat.factorization_gcd (pow_ne_zero a hp.ne_zero) hN
    simp [this]
  rw [Nat.factorization_pow_self hp] at h1
  have hdvd : Nat.gcd (p ^ a) N ∣ p ^ a := Nat.gcd_dvd_left _ _
  have ha : p ^ a ≠ 0 := pow_ne_zero a hp.ne_zero
  have hne : Nat.gcd (p ^ a) N ≠ 0 := by
    simp [Nat.gcd_eq_zero_iff, hN]
  -- Any divisor of p^a is a power of p
  have pow_form : ∀ d, d ∣ p ^ a → d ≠ 0 → ∃ k, d = p ^ k := by
    intro d hd hd0
    use d.factorization p
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hd0]
    have hsupp : d.factorization.support ⊆ {p} := by
      intro q hq
      rw [Finsupp.mem_support_iff] at hq
      rw [Finset.mem_singleton]
      -- q ∈ d.factorization.support means d.factorization q ≠ 0
      -- This implies q ∣ d (since q^(d.factorization q) ∣ d and d.factorization q ≥ 1)
      have hq_dvd : q ∣ d := Nat.dvd_trans (dvd_pow_self q (Nat.pos_of_ne_zero hq).ne') (Nat.ordProj_dvd d q)
      -- Since d ∣ p^a, we have q ∣ p^a
      have hq_dvd_pa : q ∣ p ^ a := Nat.dvd_trans hq_dvd hd
      -- Since q ∣ p^a and q is a natural number, if q is prime then q = p
      -- We need to show q is prime: this follows from q ∈ support of factorization
      have hq_prime : q.Prime := by
        by_contra hnp
        apply hq
        exact Nat.factorization_eq_zero_of_not_prime d hnp
      have hq_dvd_p : q ∣ p := Nat.Prime.dvd_of_dvd_pow hq_prime hq_dvd_pa
      exact Nat.prime_dvd_prime_iff_eq hq_prime hp |>.mp hq_dvd_p
    rw [Finsupp.prod_eq_single p (fun b hb hbp => by
      have hb_in_sup := Finsupp.mem_support_iff.mpr hb
      exact False.elim (hbp (Finset.mem_singleton.mp (hsupp hb_in_sup)))
    ) (fun _ => by simp)]
  obtain ⟨k, hk⟩ := pow_form _ hdvd hne
  rw [hk]
  congr 1
  have : (p ^ k).factorization p = min a (N.factorization p) := by rwa [← hk]
  rw [Nat.factorization_pow_self hp] at this
  exact this

/-- If `x ^ (p ^ a) = y` and `y` has order `p ^ k` then `x` has order `p ^ (a + k)`. -/
