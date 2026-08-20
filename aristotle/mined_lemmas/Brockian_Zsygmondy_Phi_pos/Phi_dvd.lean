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

lemma Phi_dvd (n a : ℕ) : Phi n a ∣ (a : ℤ) ^ n - 1 := by
  unfold Phi
  have h : cyclotomic n ℤ ∣ X ^ n - 1 := Polynomial.cyclotomic.dvd_X_pow_sub_one (R := ℤ) n
  obtain ⟨c, hc⟩ := h
  have : (a : ℤ) ^ n - 1 = Polynomial.eval (a : ℤ) (X ^ n - 1) := by simp
  rw [this, hc]
  simp [Polynomial.eval_mul]

/-- Reduction of `p ∣ Φ n a` to a root statement over `ZMod p`. -/
