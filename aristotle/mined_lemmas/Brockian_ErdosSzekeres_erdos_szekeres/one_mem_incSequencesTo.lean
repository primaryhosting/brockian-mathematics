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

private lemma one_mem_incSequencesTo : 1 ∈ incSequencesTo f i := mem_image.2 ⟨{i}, by simp⟩

/-- The singleton sequence is decreasing, so 1 is a possible length. -/
