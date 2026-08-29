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

theorem five_le_of_isPrime {p : Nat} (hp : IsPrime p) (h2 : p ≠ 2) (h3 : p ≠ 3) : 5 ≤ p := by
  rcases hp with ⟨hp2, hdvd⟩
  if h : 5 ≤ p then
    exact h
  else
    have hp4 : p = 4 := by omega
    exact absurd (show (2 : Nat) ∣ p by omega) (hdvd 2 (by omega) (by omega))

/-- **Pair criterion.** The gap tuple `{0, g}` is admissible exactly when `g` is even. -/
