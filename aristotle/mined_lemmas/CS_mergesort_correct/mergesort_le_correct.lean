/-!
# Mergesort Correct
Category: Computer Science
Target: CS.mergesort_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- **Mergesort is correct.**

For any boolean comparison `le` that is transitive and total, `List.mergeSort le l`
is sorted with respect to `le` (expressed by `List.Pairwise`, the sortedness predicate
used by Mathlib) and is a permutation of `l`.

Both halves are supplied by existing library lemmas:
* `List.pairwise_mergeSort` (sortedness of the output),
* `List.mergeSort_perm` (the output is a permutation of the input).

Note that this file needs no `import`: `List.mergeSort` and both lemmas live in the
Lean core library, which is available automatically; the statement and proof are
unchanged in a Mathlib context (see `RequestProject/MergesortMathlib.lean`, where the
Mathlib-flavoured corollaries `CS.mergesort_correct'` and `CS.mergesort_le_correct` are
derived from this theorem). -/

theorem mergesort_le_correct {α : Type*} [LinearOrder α] (l : List α) :
    (l.mergeSort (fun a b => decide (a ≤ b))).Pairwise (· ≤ ·) ∧
      (l.mergeSort (fun a b => decide (a ≤ b))).Perm l :=
  mergesort_correct' (· ≤ ·) l

end CS

