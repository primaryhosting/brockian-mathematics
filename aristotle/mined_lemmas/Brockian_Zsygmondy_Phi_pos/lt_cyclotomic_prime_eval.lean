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

lemma lt_cyclotomic_prime_eval {p y : ℕ} (hp : p.Prime) (hy : 2 ≤ y) :
    (p : ℤ) < (cyclotomic p ℤ).eval (y : ℤ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hyz : (2 : ℤ) ≤ (y : ℤ) := by exact_mod_cast hy
  rw [cyclotomic_prime ℤ p]
  simp only [eval_finset_sum, eval_pow, eval_X]
  have hlt : ∑ _i ∈ Finset.range p, (1 : ℤ) < ∑ i ∈ Finset.range p, (y : ℤ) ^ i := by
    refine Finset.sum_lt_sum (fun i _ => one_le_pow₀ (by linarith)) ⟨1, ?_, ?_⟩
    · exact Finset.mem_range.2 hp.one_lt
    · simpa using by linarith
  simpa using hlt

/-- The case `m ≥ 2` and `p ≥ 5`, via the real-analytic bounds. -/
