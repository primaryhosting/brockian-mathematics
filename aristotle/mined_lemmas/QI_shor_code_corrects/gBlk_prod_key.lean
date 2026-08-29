/-
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped BigOperators

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace QI

/-! ## Basic types

A computational basis state of one *block* of three qubits is a function `Fin 3 → Bool`;
a computational basis state of the nine qubits of the Shor code is a function
`Fin 3 → Blk`, i.e. three blocks of three qubits.  A qubit is addressed by a pair
`q : Q = Fin 3 × Fin 3` (block index, position inside the block). -/

/-- Computational basis states of one three-qubit block. -/
abbrev Blk := Fin 3 → Bool

/-- Computational basis states of the nine qubits. -/
abbrev Bas := Fin 3 → Blk

/-- Addresses of the nine qubits. -/
abbrev Q := Fin 3 × Fin 3

/-- Bitwise `xor` on a block. -/

theorem gBlk_prod_key (x z : Bas) (h : wt x z ≤ 2) (s t : Bool) :
    (∏ j, gBlk s t (x j) (z j))
      = if s = t then (∏ j, gBlk false false (x j) (z j)) else 0 := by
  by_cases hall : ∀ j, x j = zeroB
  · -- every `x j` is trivial
    by_cases hst : s = t
    · subst hst
      cases s with
      | false => simp
      | true =>
          rw [if_pos rfl]
          exact (Finset.prod_congr rfl fun j _ => by rw [hall j, ← gBlk_diag (z j)])
    · -- off-diagonal: some block carries no `z`, and there the coefficient vanishes
      have hz : ∃ j, z j = zeroB := by
        by_contra hc
        push_neg at hc
        have : 3 ≤ wt x z := by
          have : ∀ j ∈ (Finset.univ : Finset (Fin 3)), 1 ≤ wtB (x j) (z j) :=
            fun j _ => wtB_pos_of_ne_zero _ _ (hc j)
          calc (3 : ℕ) = ∑ _j : Fin 3, 1 := by simp
            _ ≤ ∑ j : Fin 3, wtB (x j) (z j) := Finset.sum_le_sum this
            _ = wt x z := rfl
        omega
      obtain ⟨j, hj⟩ := hz
      rw [if_neg hst]
      refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
      rw [hall j, hj]
      exact gBlk_offdiag_zero s t hst
  · -- some `x j` is neither `000` nor `111`, so every product vanishes
    push_neg at hall
    obtain ⟨j, hj⟩ := hall
    have hj1 : x j ≠ oneB := by
      intro hc
      have := wtB_le_wt x z j
      rw [hc, wtB_oneB (z j)] at this
      omega
    have hnc : ¬ (x j = zeroB ∨ x j = oneB) := by
      rintro (h1 | h1) <;> [exact hj h1; exact hj1 h1]
    have hzero : ∀ s t : Bool, (∏ j, gBlk s t (x j) (z j)) = 0 := fun s t =>
      Finset.prod_eq_zero (Finset.mem_univ j) (gBlk_eq_zero_of_not_const s t _ _ hnc)
    rw [hzero s t, hzero false false]
    simp

/-! ## Bilinearity of the inner product -/

