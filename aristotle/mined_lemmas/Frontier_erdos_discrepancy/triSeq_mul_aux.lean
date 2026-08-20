import Mathlib
import RequestProject.ErdosDiscrepancy
import RequestProject.ErdosDiscrepancyMathlib
import RequestProject.ErdosDiscrepancySpecialCases
import RequestProject.ErdosDiscrepancyMeasure

/-!
# The base case for completely multiplicative sequences

For a completely multiplicative `±1` sequence every homogeneous sum is `f d` times an
ordinary partial sum, so only the sums `S n = f 1 + ⋯ + f n` matter.  Tracking the four
values `f 2, f 3, f 5, f 7` shows that one of `S 4, S 6, S 8, S 10` must exceed `1` in
absolute value: for completely multiplicative sequences the length `10` already forces
discrepancy `2` (as opposed to `12` in general).
-/

namespace Frontier

/-- Unfolding the ordinary partial sums. -/

private theorem triSeq_mul_aux : ∀ s a b : ℕ, a + b = s → 1 ≤ a → 1 ≤ b →
    triSeq (a * b) = triSeq a * triSeq b := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
      intro a b hs ha hb
      by_cases h3a : a % 3 = 0
      · obtain ⟨a', rfl⟩ : ∃ a', a = 3 * a' := ⟨a / 3, by omega⟩
        have ha' : 1 ≤ a' := by omega
        rw [show 3 * a' * b = 3 * (a' * b) from by ring, triSeq_three_mul, triSeq_three_mul,
          ih (a' + b) (by omega) a' b rfl ha' hb]
      · by_cases h3b : b % 3 = 0
        · obtain ⟨b', rfl⟩ : ∃ b', b = 3 * b' := ⟨b / 3, by omega⟩
          have hb' : 1 ≤ b' := by omega
          rw [show a * (3 * b') = 3 * (a * b') from by ring, triSeq_three_mul, triSeq_three_mul,
            ih (a + b') (by omega) a b' rfl ha hb']
        · rcases (show a % 3 = 1 ∨ a % 3 = 2 by omega) with h1 | h1 <;>
            rcases (show b % 3 = 1 ∨ b % 3 = 2 by omega) with h2 | h2
          · have hab : (a * b) % 3 = 1 := by rw [Nat.mul_mod, h1, h2]
            rw [triSeq_mod_one hab, triSeq_mod_one h1, triSeq_mod_one h2]; norm_num
          · have hab : (a * b) % 3 = 2 := by rw [Nat.mul_mod, h1, h2]
            rw [triSeq_mod_two hab, triSeq_mod_one h1, triSeq_mod_two h2]; norm_num
          · have hab : (a * b) % 3 = 2 := by rw [Nat.mul_mod, h1, h2]
            rw [triSeq_mod_two hab, triSeq_mod_two h1, triSeq_mod_one h2]; norm_num
          · have hab : (a * b) % 3 = 1 := by rw [Nat.mul_mod, h1, h2]
            rw [triSeq_mod_one hab, triSeq_mod_two h1, triSeq_mod_two h2]; norm_num

/-- The base-`3` sequence is completely multiplicative. -/
