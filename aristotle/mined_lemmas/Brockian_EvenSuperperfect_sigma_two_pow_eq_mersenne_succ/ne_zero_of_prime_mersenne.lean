import Mathlib
namespace Brockian.EvenSuperperfect

namespace EuclidEuler
namespace Nat

open ArithmeticFunction Finset
open scoped sigma


theorem ne_zero_of_prime_mersenne (k : ℕ) (pr : (mersenne (k + 1)).Prime) : k ≠ 0 := by
  intro H
  simp [H, mersenne, Nat.not_prime_one] at pr

