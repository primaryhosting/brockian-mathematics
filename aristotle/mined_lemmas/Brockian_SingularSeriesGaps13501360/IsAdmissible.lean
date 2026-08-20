/-!
# Singular Series Gaps 13501360
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps13501360
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian

/-- A finite set of integers `H` is *admissible* if for every prime `p` there is a residue
class mod `p` avoided by every element of `H`.  Equivalently, `H` does not cover all residues
modulo any prime; this is exactly the condition under which the singular series
`𝔖(H) = ∏_p (1 - ν_H(p)/p)/(1 - 1/p)^{|H|}` has no vanishing local factor. -/

def IsAdmissible (H : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r

/-- The number of residues mod `p` occupied by `H`, i.e. the local factor datum `ν_H(p)`. -/
