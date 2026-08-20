import Mathlib
namespace Brockian.MsVanDerWaerden
/-- Van der Waerden's theorem: for any k and any r-coloring of the naturals, some monochromatic
    arithmetic progression of length k exists within a bounded window. -/
theorem van_der_waerden (k r : ℕ) (hk : 0 < k) (hr : 0 < r) :
    ∃ N : ℕ, ∀ c : ℕ → Fin r, ∃ a d : ℕ, 0 < d ∧
      (∀ i, i < k → a + i * d ≤ N) ∧
      (∀ i j, i < k → j < k → c (a + i * d) = c (a + j * d)) := by
  sorry
end Brockian.MsVanDerWaerden
