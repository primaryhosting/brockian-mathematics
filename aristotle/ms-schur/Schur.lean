import Mathlib
namespace Brockian.Schur
/-- Schur's theorem: for any finite coloring, some sufficiently large interval contains a
    monochromatic solution of x + y = z. -/
theorem schur (r : ℕ) (hr : 0 < r) :
    ∃ N : ℕ, 0 < N ∧ ∀ c : ℕ → Fin r,
      ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ x ≤ N ∧ y ≤ N ∧ z ≤ N ∧
        x + y = z ∧ c x = c y ∧ c y = c z := by
  sorry
end Brockian.Schur
