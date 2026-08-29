import RequestProject.SimonQuantum

/-!
# Recovering the hidden shift from the measured samples

Each run of the quantum subroutine returns a uniformly random `y ∈ s^⊥`.  After `m`
runs the classical post-processing solves the linear system `t ⬝ y_i = 0` and outputs the
unique nonzero solution, which succeeds exactly when the samples *determine* `s`.
We bound the number of sample sequences that fail to determine `s`.
-/

open scoped BigOperators

namespace QI

variable {n : ℕ}

/-- The samples `y : Fin m → BV n` determine the hidden shift `s`: the only vectors
orthogonal to all of them are `0` and `s`. -/

theorem card_badSamples_le (s : BV n) (m : ℕ) :
    2 ^ m * (badSamples s m).card ≤ 2 ^ n * (perp s).card ^ m := by
  classical
  set F : Finset (BV n) := Finset.univ.filter (fun t => t ≠ 0 ∧ t ≠ s) with hF
  set P : BV n → Finset (BV n) := fun t => (perp s).filter (fun y => dotp t y = 0) with hP
  have hsub : badSamples s m ⊆ F.biUnion (fun t => Fintype.piFinset (fun _ => P t)) := by
    intro y hy
    simp only [badSamples, allSamples, Finset.mem_filter, Fintype.mem_piFinset] at hy
    obtain ⟨hmem, hnd⟩ := hy
    rw [Determines] at hnd
    push_neg at hnd
    obtain ⟨t, htall, ht0, hts⟩ := hnd
    refine Finset.mem_biUnion.2 ⟨t, ?_, ?_⟩
    · simp [hF, ht0, hts]
    · exact Fintype.mem_piFinset.2 (fun i => Finset.mem_filter.2 ⟨hmem i, htall i⟩)
  have hcard : (badSamples s m).card ≤ ∑ t ∈ F, (P t).card ^ m := by
    refine le_trans (Finset.card_le_card hsub) ?_
    refine le_trans (Finset.card_biUnion_le) ?_
    exact Finset.sum_le_sum (fun t _ => by simp [Fintype.card_piFinset])
  calc 2 ^ m * (badSamples s m).card ≤ 2 ^ m * ∑ t ∈ F, (P t).card ^ m := by
        exact Nat.mul_le_mul_left _ hcard
    _ = ∑ t ∈ F, (2 * (P t).card) ^ m := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun t _ => by rw [mul_pow]
    _ = ∑ _t ∈ F, (perp s).card ^ m := by
        refine Finset.sum_congr rfl fun t ht => ?_
        simp only [hF, Finset.mem_filter] at ht
        rw [card_perp_filter ht.2.1 ht.2.2]
    _ = F.card * (perp s).card ^ m := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ 2 ^ n * (perp s).card ^ m := by
        refine Nat.mul_le_mul_right _ ?_
        refine le_trans (Finset.card_filter_le _ _) ?_
        simp [Finset.card_univ, ZMod.card]

/-- With `m = n + k` queries, the failure probability of Simon's algorithm is at most
`2^{-k}`: at most a `2^{-k}` fraction of the `|s^⊥|^(n+k)` sample sequences fails to
determine the hidden shift.  In particular `O(n)` quantum queries suffice. -/
