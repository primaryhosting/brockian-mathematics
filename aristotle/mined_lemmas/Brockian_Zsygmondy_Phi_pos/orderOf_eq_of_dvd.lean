import Mathlib
namespace Brockian.Zsygmondy

open Polynomial

/-! ## Auxiliary results

The proof follows the classical cyclotomic-polynomial argument (Bang's theorem).
Write `Φ n a = eval (a : ℤ) (cyclotomic n ℤ)`.

* Any prime `q ∣ Φ n a` with `q ∤ n` is a primitive prime divisor of `aⁿ - 1`.
* If a prime `p ∣ Φ n a` divides `n`, writing `n = p ^ k * m` with `p ∤ m`, then the
  multiplicative order of `a` mod `p` is exactly `m`, hence `m ∣ p - 1`; in particular `p` is
  the largest prime factor of `n`, and `p ^ 2 ∤ Φ n a`.
* Consequently, if `Φ n a` has no prime factor coprime to `n`, then `Φ n a = p`.
* Finally `Φ n a > p`, a contradiction (except for `(a, n) = (2, 6)`).
-/

/-- The value of the `n`-th cyclotomic polynomial at a natural number `a`, as an integer. -/

lemma orderOf_eq_of_dvd {a p k m : ℕ} (hp : p.Prime) (hpm : ¬ p ∣ m)
    (hdvd : (p : ℤ) ∣ Phi (p ^ k * m) a) : orderOf (a : ZMod p) = m := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero ((m : ZMod p)) := NeZero.of_not_dvd (ZMod p) hpm
  have hroot := isRoot_zmod_of_dvd_Phi hdvd
  have h := (isRoot_cyclotomic_prime_pow_mul_iff_of_charP (R := ZMod p) (p := p) (m := m)
    (k := k)).1 hroot
  exact h.eq_orderOf.symm

/-- If `p ∣ n` and `p ∣ Φ n a`, then the prime-to-`p` part of `n` divides `p - 1`. -/
