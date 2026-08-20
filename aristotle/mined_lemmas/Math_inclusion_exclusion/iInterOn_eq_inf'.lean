/-
# Inclusion Exclusion
Category: Pure Mathematics
Target: Math.inclusion_exclusion
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Inclusion Exclusion

Formalisation of the inclusion-exclusion principle:
`|⋃_{i ∈ s} A i| = Σ_{∅ ≠ t ⊆ s} (−1)^{|t|+1} |⋂_{i ∈ t} A i|`.
-/

open Finset

namespace Math

/-- The intersection `⋂_{i ∈ t} A i`, realised as a `Finset` by carving it out of the
ambient union `⋃_{i ∈ s} A i`.  For nonempty `t ⊆ s` this is genuinely the intersection
of the family `(A i)_{i ∈ t}` (see `Math.iInter_eq_inf'`). -/

lemma iInterOn_eq_inf' {ι α : Type*} [DecidableEq α] {s : Finset ι} (A : ι → Finset α)
    {t : Finset ι} (hts : t ⊆ s) (ht : t.Nonempty) :
    iInterOn s A t = t.inf' ht A := by
  ext a
  rw [mem_iInterOn, Finset.mem_inf' ht]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  obtain ⟨i, hi⟩ := ht
  exact ⟨i, hts hi, h i hi⟩

/-- **Inclusion–exclusion principle**:
`|⋃_{i ∈ s} A i| = Σ_{∅ ≠ t ⊆ s} (−1)^{|t|+1} |⋂_{i ∈ t} A i|`. -/
