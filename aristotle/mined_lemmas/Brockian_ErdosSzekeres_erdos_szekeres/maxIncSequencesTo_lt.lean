import Mathlib

/-!
# Erdős–Szekeres theorem

Any injective sequence of `r * s + 1` reals has a strictly increasing subsequence of length
`r + 1` or a strictly decreasing subsequence of length `s + 1`.

The proof is the classical pigeonhole argument: label each index `i` with the pair consisting of
the maximal length of an increasing subsequence ending at `i` and the maximal length of a
decreasing subsequence ending at `i`; these pairs are pairwise distinct, so if all increasing
sequences had length `≤ r` and all decreasing ones length `≤ s`, there would be at most `r * s`
indices.
-/

open Function Finset

namespace Brockian.ErdosSzekeres

section Aux

variable {α β : Type*} [Fintype α] [LinearOrder α] [LinearOrder β] {f : α → β} {i : α}

/-- The possible lengths of an increasing sequence which ends at `i`. -/
private noncomputable def incSequencesTo (f : α → β) (i : α) : Finset ℕ :=
  open Classical in
  image card {t : Finset α | IsGreatest t i ∧ StrictMonoOn f t}

/-- The possible lengths of a decreasing sequence which ends at `i`. -/
private noncomputable def decSequencesTo (f : α → β) (i : α) : Finset ℕ :=
  open Classical in
  image card {t : Finset α | IsGreatest t i ∧ StrictAntiOn f t}

/-- The singleton sequence is increasing, so 1 is a possible length. -/

private lemma maxIncSequencesTo_lt {i j : α} (hij : i < j) (hfij : f i < f j) :
    maxIncSequencesTo f i < maxIncSequencesTo f j := by
  classical
  rw [Nat.lt_iff_add_one_le]
  refine le_max' _ _ ?_
  have : maxIncSequencesTo f i ∈ incSequencesTo f i := max'_mem _ incSequencesTo_nonempty
  simp only [incSequencesTo, mem_image, mem_filter, mem_univ, true_and, and_assoc] at this
  obtain ⟨t, hti, ht₁, ht₂⟩ := this
  simp only [incSequencesTo, mem_image, mem_filter, mem_univ, true_and, and_assoc]
  have hlt : ∀ x ∈ t, x < j := fun x hx ↦ (hti.2 hx).trans_lt hij
  refine ⟨insert j t, ?_, ?_, ?_⟩
  next =>
    convert hti.insert j using 1
    next => simp
    next => rw [max_eq_left hij.le]
  next =>
    simp only [coe_insert]
    rw [strictMonoOn_insert_iff_of_forall_le]
    · refine ⟨?_, ht₁⟩
      intro x hx hxj
      exact (ht₁.monotoneOn hx hti.1 (hti.2 hx)).trans_lt hfij
    · exact fun x hx ↦ (hlt x hx).le
  have hj : j ∉ t := fun hj ↦ lt_irrefl _ (hlt _ hj)
  simp [hj, ht₂]

