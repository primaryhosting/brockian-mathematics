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

def iInterOn {ι α : Type*} [DecidableEq α] (s : Finset ι) (A : ι → Finset α) (t : Finset ι) :
    Finset α :=
  (s.biUnion A).filter (fun a => ∀ i ∈ t, a ∈ A i)

