import Mathlib
namespace Frontier.CryptoComplexity
open Function

/-- The one-time pad map `k ↦ m ^^^ k` is a bijection, since it is an involution. -/

theorem boolean_function_count (n : ℕ) :
    Fintype.card ((Fin n → Bool) → Bool) = 2 ^ (2 ^ n) := by
  simp

end Frontier.CryptoComplexity

