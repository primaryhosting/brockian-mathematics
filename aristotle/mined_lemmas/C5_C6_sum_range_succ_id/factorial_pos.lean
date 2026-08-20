import Mathlib
open Finset
namespace C5.C6

/-- Gauss' summation formula, in the doubled form `2 * ∑_{i<n+1} i = n(n+1)`.
See `Finset.sum_range_id_mul_two` in Mathlib. -/

theorem factorial_pos (n : ℕ) : 0 < n.factorial := Nat.factorial_pos n

end C5.C6

