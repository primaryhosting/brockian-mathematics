import Mathlib
namespace Brockian.PseudoprimesBaseTwo

/-! ### Cipolla's construction

For an odd prime `p ≥ 5` the number `N p = (4 ^ p - 1) / 3 = (2 ^ p - 1) * ((2 ^ p + 1) / 3)`
is a Fermat pseudoprime to base 2. -/

/-- `A p = 2 ^ p - 1`. -/

theorem infinite_pseudoprimes_base_two :
    {n : ℕ | ¬ n.Prime ∧ 1 < n ∧ 2 ^ n ≡ 2 [MOD n]}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  obtain ⟨p, hpa, hp⟩ := Nat.exists_infinite_primes (max (a + 1) 5)
  have h5 : 5 ≤ p := le_trans (le_max_right _ _) hpa
  have hap : a < p := lt_of_lt_of_le (Nat.lt_succ_self a) (le_trans (le_max_left _ _) hpa)
  exact ⟨N p, ⟨N_not_prime h5, one_lt_N h5, pow_N_modEq hp h5⟩,
    lt_trans hap (lt_N h5)⟩

end Brockian.PseudoprimesBaseTwo

