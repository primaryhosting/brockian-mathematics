import Mathlib
namespace Brockian.MsThue
/-- Thue's lemma: for n > 1 and any a, there exist x, y not both zero with |x|,|y| ≤ √n and
    x ≡ a·y (mod n). -/
theorem thue_lemma (n a : ℕ) (hn : 1 < n) :
    ∃ x y : ℤ, (x ≠ 0 ∨ y ≠ 0) ∧ x.natAbs ≤ Nat.sqrt n ∧ y.natAbs ≤ Nat.sqrt n ∧
      (n : ℤ) ∣ (x - a * y) := by
  sorry
end Brockian.MsThue
