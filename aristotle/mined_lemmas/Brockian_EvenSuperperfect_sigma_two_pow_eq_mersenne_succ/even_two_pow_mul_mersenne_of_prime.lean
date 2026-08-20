import Mathlib
namespace Brockian.EvenSuperperfect

namespace EuclidEuler
namespace Nat

open ArithmeticFunction Finset
open scoped sigma


theorem even_two_pow_mul_mersenne_of_prime (k : ℕ) (pr : (mersenne (k + 1)).Prime) :
    Even (2 ^ k * mersenne (k + 1)) := by simp [ne_zero_of_prime_mersenne k pr, parity_simps]

