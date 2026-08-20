import Mathlib
namespace Brockian.CatalanClosed
/-- Closed form for the Catalan numbers: (n+1)·Cₙ = C(2n, n). -/
theorem succ_mul_catalan_eq_choose (n : ℕ) :
    (n + 1) * Nat.catalan n = Nat.choose (2 * n) n := by
  sorry
end Brockian.CatalanClosed
