import Mathlib
/-!
# Chen Theorem
Category: Frontier — Prime Numbers
Target: Frontier.Chen_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- `q` is *almost prime of order 2*: it has at most two prime factors, counted with
multiplicity (i.e. `Ω q ≤ 2`, so `q` is `1`, a prime, or a product of two primes). -/

theorem chen_base_case (n : ℕ) (h4 : 4 ≤ n) (h200 : n ≤ 200) (hn : Even n) :
    ChenRepresentation n := by
  obtain ⟨p, -, q, -, hp, hq, hpq⟩ :=
    goldbach_below_201 n (by omega) h4 (Nat.even_iff.mp hn)
  exact ⟨p, q, hp, almostPrime2_of_prime hq, hpq⟩

/-- Reduction: the Goldbach conjecture implies Chen's theorem (with `N = 4`), since a prime
is in particular a product of at most two primes. -/
