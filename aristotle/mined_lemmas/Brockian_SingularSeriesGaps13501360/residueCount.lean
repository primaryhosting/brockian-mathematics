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

noncomputable def residueCount (H : Finset ℤ) (p : ℕ) : ℕ :=
  (H.image (fun x : ℤ => (x : ZMod p))).card

/-- Admissibility is equivalent to the statement that every local factor
`1 - ν_H(p)/p` of the singular series is nonzero. -/
