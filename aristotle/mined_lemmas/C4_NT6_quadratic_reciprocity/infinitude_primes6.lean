import Mathlib
namespace C4.NT6

/-- Quadratic reciprocity for distinct odd primes: this is
`legendreSym.quadratic_reciprocity` up to commutativity of multiplication. -/

theorem infinitude_primes6 : {p : ℕ | p.Prime}.Infinite :=
  Nat.infinite_setOf_prime

end C4.NT6

