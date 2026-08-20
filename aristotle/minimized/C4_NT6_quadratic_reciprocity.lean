import Mathlib
namespace C4.NT6

/-- Quadratic reciprocity for distinct odd primes: this is
`legendreSym.quadratic_reciprocity` up to commutativity of multiplication. -/

theorem quadratic_reciprocity (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hp : p ≠ 2) (hq : q ≠ 2) (hpq : p ≠ q) :
    legendreSym p q * legendreSym q p = (-1) ^ ((p/2) * (q/2)) := by
  rw [mul_comm]
  exact legendreSym.quadratic_reciprocity hp hq hpq

/-- Euler's criterion: a nonzero residue mod an odd prime `p` is a square iff
`a ^ ((p-1)/2) = 1`. -/
