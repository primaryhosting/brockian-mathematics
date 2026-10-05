import Mathlib
/-!
# Halls Marriage
Category: Pure Mathematics
Target: Math.halls_marriage
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
A self-contained development of Hall's marriage theorem.

* `Math.hall_exists_injective_iff` : the combinatorial ("system of distinct representatives")
  form, proved from scratch by induction (it does *not* use Mathlib's Hall theorem).
* `Math.halls_marriage` : a bipartite graph has a perfect matching iff Hall's condition holds.
-/

namespace Math

open Finset

section Core

variable {ι α : Type*} [DecidableEq ι] [DecidableEq α]

omit [DecidableEq ι] in

private theorem biUnion_sdiff (t : ι → Finset α) (w : Finset α) (u : Finset ι) :
    (u.biUnion fun i => t i \ w) = (u.biUnion t) \ w := by
  ext y
  simp only [Finset.mem_biUnion, Finset.mem_sdiff]
  constructor
  · rintro ⟨i, hi, hy1, hy2⟩; exact ⟨⟨i, hi, hy1⟩, hy2⟩
  · rintro ⟨⟨i, hi, hy1⟩, hy2⟩; exact ⟨i, hi, hy1, hy2⟩

/-- Auxiliary induction: with an upper bound `n` on the cardinality of `s`, Hall's condition
on all subsets of `s` yields a system of distinct representatives for `s`. -/
