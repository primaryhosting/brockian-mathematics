import Mathlib
namespace Brockian.OddPerfectThreePrimes

open Finset

/-- For a prime `p`, `(p-1) * σ₁(p^a) = p^(a+1) - 1 < p * p^a`. -/

private lemma sum_divisors_prod (s : Finset ℕ) (f : ℕ → ℕ) :
    (∀ p ∈ s, ∀ q ∈ s, p ≠ q → Nat.Coprime (f p) (f q)) → (∀ p ∈ s, f p ≠ 0) →
    ∑ d ∈ (∏ p ∈ s, f p).divisors, d = ∏ p ∈ s, ∑ d ∈ (f p).divisors, d := by
  classical
  induction s using Finset.induction_on with
  | empty => intro _ _; simp
  | @insert a s ha ih =>
    intro hcop hne
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hcop_a : Nat.Coprime (f a) (∏ p ∈ s, f p) :=
      Nat.Coprime.prod_right fun q hq =>
        hcop a (Finset.mem_insert_self a s) q (Finset.mem_insert_of_mem hq)
          (by rintro rfl; exact ha hq)
    rw [Nat.Coprime.sum_divisors_mul hcop_a,
      ih (fun p hp q hq hpq =>
            hcop p (Finset.mem_insert_of_mem hp) q (Finset.mem_insert_of_mem hq) hpq)
         (fun p hp => hne p (Finset.mem_insert_of_mem hp))]

/-- Multiplicative bound: `(∏ (p-1)) * σ₁(n) < (∏ p) * n` for `n` with at least one prime
factor. -/
