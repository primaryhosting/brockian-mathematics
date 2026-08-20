/-
# Singular Series Gaps 16021610
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps16021610
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Singular Series Gaps 16021610
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps16021610
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-- A finite set of integers `H` is *admissible* (in the sense of the Hardy–Littlewood
prime `k`-tuples conjecture) if for every prime `p` the elements of `H` do not cover all
residue classes modulo `p`.  Equivalently, the local factor of the singular series
`𝔖(H) = ∏_p (1 - 1/p)^{-|H|} (1 - ν_p(H)/p)` is nonzero at every prime. -/

theorem gapTuple_range :
    (0 : ℤ) ∈ gapTuple ∧ (26 : ℤ) ∈ gapTuple ∧ ∀ h ∈ gapTuple, 0 ≤ h ∧ h ≤ 26 := by
  refine ⟨by decide, by decide, ?_⟩
  decide

