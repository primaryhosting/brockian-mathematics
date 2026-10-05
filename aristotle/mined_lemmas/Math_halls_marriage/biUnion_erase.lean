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

private theorem biUnion_erase (t : ι → Finset α) (x : α) (u : Finset ι) :
    (u.biUnion fun i => (t i).erase x) = (u.biUnion t).erase x := by
  ext y
  simp only [Finset.mem_biUnion, Finset.mem_erase]
  constructor
  · rintro ⟨i, hi, hy1, hy2⟩; exact ⟨hy1, i, hi, hy2⟩
  · rintro ⟨hy1, i, hi, hy2⟩; exact ⟨i, hi, hy1, hy2⟩

omit [DecidableEq ι] in
