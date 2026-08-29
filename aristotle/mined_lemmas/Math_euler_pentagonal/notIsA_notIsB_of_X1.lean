import Mathlib

/-!
# Franklin's involution and the pentagonal number theorem (combinatorial core)

A partition of `n` into distinct positive parts is encoded as a `Finset ℕ` not containing `0`
whose sum is `n`.  The main result of this file, `Franklin.sum_sign_DP`, is Franklin's theorem:
the signed count `∑ (-1)^(number of parts)` over all partitions of `n` into distinct parts is
`(-1)^k` if `n` is a generalized pentagonal number `k(3k∓1)/2`, and `0` otherwise.
-/

namespace Franklin

open Finset

/-- Partitions of `n` into distinct positive parts, encoded as finsets of positive naturals. -/

lemma notIsA_notIsB_of_X1 {s : Finset ℕ} (h0 : 0 ∉ s) (hshape : s = Finset.Ico s.card (2 * s.card)) :
    ¬IsA s ∧ ¬IsB s := by
  set k := s.card with hk
  rcases Nat.eq_zero_or_pos k with hk0 | hk1
  · have hemp : s = ∅ := by rw [hshape, hk0]; simp
    constructor
    · rintro ⟨hs, -⟩; rw [hemp] at hs; exact absurd hs (by simp)
    · rintro ⟨hs, -⟩; rw [hemp] at hs; exact absurd hs (by simp)
  · have hmn : mn s = k := by rw [hshape]; exact mn_Ico (by omega)
    have hrun : run s = k := by rw [hshape, run_Ico (by omega) (by omega)]; omega
    constructor
    · rintro ⟨-, -, hex⟩
      exact hex ⟨by omega, by omega⟩
    · rintro ⟨-, hlt, -⟩
      omega

