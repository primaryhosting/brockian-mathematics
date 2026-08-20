/-
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- A `±1`-sequence: a function `f : ℕ → ℤ` all of whose values on positive integers
are `1` or `-1`. -/

theorem exists_discrepancy_le_one_up_to_eleven :
    ∃ f : ℕ → ℤ, IsPlusMinusOne f ∧
      ∀ d n : ℕ, 0 < d → 0 < n → d * n ≤ 11 → |apSum f d n| ≤ 1 := by
  refine ⟨extremalEleven, ?_, ?_⟩
  · intro n hn
    by_cases h : n ≤ 11
    · interval_cases n <;> simp [extremalEleven]
    · exact Or.inl (by simp [extremalEleven, List.getD, show 12 ≤ n by omega])
  · intro d n hd hn hdn
    have hd11 : d ≤ 11 := le_trans (Nat.le_mul_of_pos_right d hn) hdn
    have hn11 : n ≤ 11 := le_trans (Nat.le_mul_of_pos_left n hd) hdn
    exact extremalEleven_bound_aux d (Finset.mem_Icc.mpr ⟨hd, hd11⟩) n
      (Finset.mem_Icc.mpr ⟨hn, hn11⟩) hdn

/-- The base case proved above is exactly the `C = 1` instance of the full Erdős
discrepancy statement `Frontier.ErdosDiscrepancyStatement`. -/
