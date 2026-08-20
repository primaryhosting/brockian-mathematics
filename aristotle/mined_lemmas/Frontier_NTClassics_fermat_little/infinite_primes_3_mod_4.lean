import Mathlib
namespace Frontier.NTClassics


theorem infinite_primes_3_mod_4 : {p : ℕ | p.Prime ∧ p % 4 = 3}.Infinite := by
  have h := Nat.infinite_setOf_prime_and_modEq (q := 4) (a := 3) (by norm_num) (by decide)
  convert h using 3

end Frontier.NTClassics

