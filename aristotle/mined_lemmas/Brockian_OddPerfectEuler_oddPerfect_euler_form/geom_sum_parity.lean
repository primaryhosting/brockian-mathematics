/-
  Aristotle target — Euler's theorem on odd perfect numbers (a genuine hard partial
  result toward the ancient odd-perfect-number problem; existence remains OPEN).

  If n is odd and perfect, then n has Euler's form n = p^k * m^2 with p prime,
  p ≡ 1 (mod 4), k ≡ 1 (mod 4), and p ∤ m.
-/
import Mathlib

namespace Brockian.OddPerfectEuler

open ArithmeticFunction


private lemma geom_sum_parity {p e : ℕ} (hp : p % 2 = 1) :
    (∑ i ∈ Finset.range (e + 1), p ^ i) % 2 = (e + 1) % 2 := by
  have hpi : ∀ i, p ^ i % 2 = 1 := fun i => Nat.pow_mod p i 2 ▸ by simp [hp]
  simp [Finset.sum_nat_mod, hpi]

