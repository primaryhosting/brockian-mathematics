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

lemma orderOf_eq_of_not_dvd {n a p : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ n)
    (hdvd : (p : ℤ) ∣ Phi n a) : orderOf (a : ZMod p) = n := by
  have hroot := isRoot_zmod_of_dvd_Phi hdvd
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero (n : ZMod p) := by
    refine ⟨?_⟩
    intro h
    apply hpn
    exact (ZMod.natCast_eq_zero_iff n p).mp h
  have hprim : IsPrimitiveRoot (a : ZMod p) n := (Polynomial.isRoot_cyclotomic_iff).mp hroot
  exact hprim.eq_orderOf.symm

/-- Primitivity: if `a` has order `n` modulo `p`, then `p` divides no `aᵐ - 1` with `0 < m < n`. -/
