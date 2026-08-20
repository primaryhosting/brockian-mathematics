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

lemma isRoot_zmod_of_dvd_Phi {n a p : ℕ} (hdvd : (p : ℤ) ∣ Phi n a) :
    (cyclotomic n (ZMod p)).IsRoot (a : ZMod p) := by
  unfold Phi at hdvd
  rw [Polynomial.IsRoot]
  have h1 : (cyclotomic n (ZMod p)).eval (a : ZMod p) =
      Int.cast ((cyclotomic n ℤ).eval (a : ℤ)) := by
    have hmap : cyclotomic n (ZMod p) = (cyclotomic n ℤ).map (Int.castRingHom (ZMod p)) :=
      (map_cyclotomic_int n (ZMod p)).symm
    rw [hmap, Polynomial.eval_map]
    induction (cyclotomic n ℤ) using Polynomial.induction_on' with
    | add p q hp hq => simp [Polynomial.eval₂_add, hp, hq]
    | monomial n c => simp [Polynomial.eval₂_monomial, Polynomial.eval_monomial]
  rw [h1]
  obtain ⟨k, hk⟩ := hdvd
  simp [hk]

/-! ### Primes not dividing `n` -/

