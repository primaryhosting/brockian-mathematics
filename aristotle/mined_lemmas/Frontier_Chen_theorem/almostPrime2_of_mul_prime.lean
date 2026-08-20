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

theorem almostPrime2_of_mul_prime {a b : ℕ} (ha : a.Prime) (hb : b.Prime) :
    AlmostPrime2 (a * b) := by
  have h : ArithmeticFunction.cardFactors (a * b) = 2 := by
    rw [ArithmeticFunction.cardFactors_mul ha.ne_zero hb.ne_zero,
      ArithmeticFunction.cardFactors_apply, ArithmeticFunction.cardFactors_apply,
      Nat.primeFactorsList_prime ha, Nat.primeFactorsList_prime hb]
    rfl
  rw [almostPrime2_iff_cardFactors, h]

/-- `n` admits a *Chen representation*: `n = p + q` with `p` prime and `q` having at most
two prime factors. This is the conclusion of Chen's theorem. -/
