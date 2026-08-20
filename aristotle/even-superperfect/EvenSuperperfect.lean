import Mathlib
namespace Brockian.EvenSuperperfect
open ArithmeticFunction in
/-- Even superperfect characterization: an even n satisfies σ(σ(n)) = 2n iff n = 2^(p−1)
    with 2^p − 1 a (Mersenne) prime. Uses ArithmeticFunction.sigma (Nat.sigma does not exist). -/
theorem even_superperfect_iff (n : ℕ) (hn : 0 < n) (he : Even n) :
    ArithmeticFunction.sigma 1 (ArithmeticFunction.sigma 1 n) = 2 * n ↔
      ∃ p : ℕ, (2 ^ p - 1).Prime ∧ n = 2 ^ (p - 1) := by
  sorry
end Brockian.EvenSuperperfect
