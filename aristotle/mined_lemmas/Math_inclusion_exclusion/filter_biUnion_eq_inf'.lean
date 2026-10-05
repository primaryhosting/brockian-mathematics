/-
# Inclusion Exclusion
Category: Pure Mathematics
Target: Math.inclusion_exclusion
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Math

open Finset

/-- The finset of elements of `⋃ i ∈ s, A i` lying in every `A i` for `i ∈ t` is exactly
`t.inf' ht A`, provided `t` is nonempty and `t ⊆ s`. -/

theorem filter_biUnion_eq_inf' {ι α : Type*} [DecidableEq α] {s t : Finset ι} (hts : t ⊆ s)
    (htne : t.Nonempty) (A : ι → Finset α) :
    ((s.biUnion A).filter (fun a => ∀ i ∈ t, a ∈ A i)) = t.inf' htne A := by
  ext a
  simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.inf'_eq_inf,
    Finset.mem_inf'_iff_forall (s := t)]
  constructor
  · rintro ⟨-, h⟩
    exact h
  · intro h
    obtain ⟨i, hi⟩ := htne
    exact ⟨⟨i, hts hi, h i hi⟩, h⟩

/-- **Inclusion–exclusion principle.**

For a finite family `A : ι → Finset α` indexed by `i ∈ s`, the cardinality of the union
`⋃ i ∈ s, A i` equals `∑ (-1)^(|t|+1) * |⋂ i ∈ t, A i|`, the sum ranging over the nonempty
subfamilies `t ⊆ s`.

Here the intersection `⋂ i ∈ t, A i` is realised as the finset of elements of the union that
belong to every `A i` with `i ∈ t`.

This is deduced from `Finset.inclusion_exclusion_card_biUnion` in Mathlib. -/
