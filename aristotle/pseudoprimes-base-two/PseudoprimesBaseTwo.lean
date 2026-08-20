import Mathlib
namespace Brockian.PseudoprimesBaseTwo
/-- Cipolla: there are infinitely many Fermat pseudoprimes to base 2
    (composite n > 1 with 2^n ≡ 2 mod n). -/
theorem infinite_pseudoprimes_base_two :
    {n : ℕ | ¬ n.Prime ∧ 1 < n ∧ 2 ^ n ≡ 2 [MOD n]}.Infinite := by
  sorry
end Brockian.PseudoprimesBaseTwo
