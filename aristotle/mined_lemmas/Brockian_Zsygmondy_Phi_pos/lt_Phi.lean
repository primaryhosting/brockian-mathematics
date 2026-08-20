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

lemma lt_Phi {n a p k m : ℕ} (ha : 2 ≤ a) (hp : p.Prime) (hk : 0 < k) (hmp : m ∣ p - 1)
    (hn : n = p ^ k * m) (hexc : ¬ (a = 2 ∧ n = 6)) : (p : ℤ) < Phi n a := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hp2 : 2 ≤ p := hp.two_le
  have hy2 : 2 ≤ a ^ (p ^ k') := by
    calc 2 ≤ a := ha
      _ = a ^ 1 := (pow_one a).symm
      _ ≤ a ^ (p ^ k') := Nat.pow_le_pow_right (by omega) (Nat.one_le_pow _ _ (by omega))
  have hrw : Phi n a = (cyclotomic (m * p) ℤ).eval ((a ^ (p ^ k') : ℕ) : ℤ) := by
    unfold Phi
    rw [hn, Phi_pow_reduction hp k' (a : ℤ)]
    push_cast
    ring_nf
  rw [hrw]
  refine lt_cyclotomic_mul_prime_eval hp hmp hy2 ?_
  rintro ⟨hy, hm2, hp3⟩
  have hk'0 : k' = 0 := by
    by_contra hne
    have h1 : 1 ≤ k' := by omega
    have : 2 ≤ p ^ k' := by
      calc 2 ≤ p := hp2
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ k' := Nat.pow_le_pow_right (by omega) h1
    have : 2 ^ 2 ≤ a ^ (p ^ k') := by
      calc (2:ℕ) ^ 2 ≤ a ^ 2 := Nat.pow_le_pow_left ha 2
        _ ≤ a ^ (p ^ k') := Nat.pow_le_pow_right (by omega) this
    omega
  subst hk'0
  have ha2 : a = 2 := by
    simpa using hy
  refine hexc ⟨ha2, ?_⟩
  rw [hn, hm2, hp3]
  norm_num

/-! ## Main theorem -/

/-- Zsygmondy's theorem (Bang's case b=1, n ≥ 3): aⁿ − 1 has a primitive prime divisor —
    a prime dividing aⁿ − 1 but no aᵐ − 1 for 0 < m < n — except for (a,n) = (2,6). -/
