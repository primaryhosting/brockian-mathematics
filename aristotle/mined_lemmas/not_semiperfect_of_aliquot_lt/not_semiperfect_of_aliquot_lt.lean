import Mathlib


theorem not_semiperfect_of_aliquot_lt {n : ℕ} (h : aliquot n < n) :
    ¬ Semiperfect n := by
  rintro ⟨s, hs, hsum⟩
  rw [Finset.mem_powerset] at hs
  have hle : ∑ d ∈ s, d ≤ ∑ d ∈ n.properDivisors, d :=
    Finset.sum_le_sum_of_subset (f := fun d => d) hs
  rw [hsum] at hle
  exact absurd (hle.trans_lt h) (lt_irrefl n)

