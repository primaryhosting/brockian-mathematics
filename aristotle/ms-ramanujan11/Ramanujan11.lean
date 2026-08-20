import Mathlib
namespace Brockian.MsRamanujan11
/-- Ramanujan's congruence: p(11n+6) ≡ 0 (mod 11). -/
theorem ramanujan_eleven (n : ℕ) : 11 ∣ Fintype.card (Nat.Partition (11 * n + 6)) := by
  sorry
end Brockian.MsRamanujan11
