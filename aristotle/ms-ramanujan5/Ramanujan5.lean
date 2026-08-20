import Mathlib
namespace Brockian.Ramanujan5
/-- Ramanujan's congruence: the partition function satisfies p(5n+4) ≡ 0 (mod 5). -/
theorem ramanujan_five (n : ℕ) : 5 ∣ Fintype.card (Nat.Partition (5 * n + 4)) := by
  sorry
end Brockian.Ramanujan5
