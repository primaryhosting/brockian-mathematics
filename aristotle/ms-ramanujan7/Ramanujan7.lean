import Mathlib
namespace Brockian.Ramanujan7
/-- Ramanujan's congruence: p(7n+5) ≡ 0 (mod 7). -/
theorem ramanujan_seven (n : ℕ) : 7 ∣ Fintype.card (Nat.Partition (7 * n + 5)) := by
  sorry
end Brockian.Ramanujan7
