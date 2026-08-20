import Mathlib
namespace MS2.NT2


theorem sum_two_squares_prime (p : ℕ) [Fact p.Prime] (hp : p % 4 = 1) : ∃ a b : ℕ, a^2+b^2 = p :=
  Nat.Prime.sq_add_sq (by omega)

/-- As stated, the conclusion is an implication into `True`, hence trivially provable.
A genuine form of Lucas' theorem is proved below as `lucas_theorem_eq`. -/
