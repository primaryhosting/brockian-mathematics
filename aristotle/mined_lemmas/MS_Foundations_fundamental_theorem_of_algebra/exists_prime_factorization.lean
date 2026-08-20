import Mathlib
namespace MS.Foundations


theorem exists_prime_factorization (n : ℕ) (hn : 2 ≤ n) :
    ∃ l : Multiset ℕ, (∀ p ∈ l, p.Prime) ∧ l.prod = n :=
  ⟨(n.primeFactorsList : Multiset ℕ), fun _ hp => Nat.prime_of_mem_primeFactorsList hp,
    by simpa using Nat.prod_primeFactorsList (by omega)⟩

end MS.Foundations

