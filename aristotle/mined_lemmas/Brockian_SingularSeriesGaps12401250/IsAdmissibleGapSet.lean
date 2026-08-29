/-!
# Singular Series Gaps 12401250
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps12401250
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian

/-- Primality of a natural number, stated in the usual way: `p ≥ 2` and every divisor of `p`
is `1` or `p`. (Spelled out here so that this file is fully self-contained.) -/

def IsAdmissibleGapSet (H : List Nat) : Prop :=
  ∀ p : Nat, IsPrimeNat p → ∃ r, r < p ∧ ∀ h ∈ H, h % p ≠ r

/-- For every even gap `g`, the two-element pattern `{0, g}` is admissible. -/
