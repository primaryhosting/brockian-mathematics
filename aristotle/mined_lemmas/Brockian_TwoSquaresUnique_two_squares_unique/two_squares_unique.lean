import Mathlib
namespace Brockian.TwoSquaresUnique

/-- If `p` is prime and `p = a^2 + b^2`, then `a > 0`. -/

theorem two_squares_unique {p a b c d : ℕ} (hp : p.Prime) (hp1 : p % 4 = 1)
    (hab : p = a ^ 2 + b ^ 2) (hcd : p = c ^ 2 + d ^ 2)
    (h1 : a ≤ b) (h2 : c ≤ d) : a = c ∧ b = d := by
  have hc : 0 < c := pos_of_prime_sq_add_sq hp hcd
  have hdpos : 0 < d := pos_of_prime_sq_add_sq hp (by rw [hcd, add_comm] : p = d ^ 2 + c ^ 2)
  have hcop1 : Nat.Coprime a b := coprime_of_prime_sq_add_sq hp hab
  have hcop2 : Nat.Coprime c d := coprime_of_prime_sq_add_sq hp hcd
  rcases mul_eq_mul_of_two_reps hp hab hcd with h | h
  · exact eq_of_mul_eq_mul_coprime hcop1 hcop2 hc h
  · have := eq_of_mul_eq_mul_coprime hcop1 hcop2.symm hdpos h
    omega

end Brockian.TwoSquaresUnique

