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

lemma notIsA_notIsB_of_X2 {s : Finset ℕ} (h0 : 0 ∉ s)
    (hshape : s = Finset.Ico (s.card + 1) (2 * s.card + 1)) (hne : s.card ≠ 0) :
    ¬IsA s ∧ ¬IsB s := by
  set k := s.card with hk
  have hk1 : 1 ≤ k := by omega
  have hmn : mn s = k + 1 := by rw [hshape]; exact mn_Ico (by omega)
  have hrun : run s = k := by rw [hshape, run_Ico (by omega) (by omega)]; omega
  constructor
  · rintro ⟨-, hle, -⟩
    omega
  · rintro ⟨-, -, hex⟩
    exact hex ⟨by omega, by omega⟩

