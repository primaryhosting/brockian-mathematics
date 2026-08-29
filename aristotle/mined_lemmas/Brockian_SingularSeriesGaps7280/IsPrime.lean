/-!
# Singular Series Gaps 7280
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps7280
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian

/-- `IsPrime p` : `p` is at least `2` and has no divisor `d` with `2 ≤ d < p`. -/

def IsPrime (p : Nat) : Prop := 2 ≤ p ∧ ∀ d : Nat, d < p → 2 ≤ d → ¬ (d ∣ p)

instance (p : Nat) : Decidable (IsPrime p) := by
  unfold IsPrime; infer_instance

/-- A finite tuple of integers `H` is *admissible* when for every prime `p` it omits at
least one residue class modulo `p`; equivalently, every local factor
`(1 - ν_H(p)/p)(1 - 1/p)^{-|H|}` of the Hardy–Littlewood singular series is nonzero, so
that the singular series itself does not vanish. -/
