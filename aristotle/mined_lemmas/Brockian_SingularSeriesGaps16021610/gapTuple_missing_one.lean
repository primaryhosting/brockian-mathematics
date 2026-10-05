/-!
# Singular Series Gaps 16021610
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps16021610
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-- Primality of a natural number: `2 ≤ p` and the only divisors of `p` are `1` and `p`.
(This is the usual notion of a prime natural number.) -/

theorem gapTuple_missing_one {p : Nat} (hp : 26 < p) : ∀ h ∈ gapTuple, h % p ≠ 1 := by
  intro h hh
  have hle : h ≤ 26 := by revert h; decide
  have hne : h ≠ 1 := by revert h hh; decide
  rw [Nat.mod_eq_of_lt (by omega)]
  exact hne

/-- The pattern `{0, 2, 6, 8, 12, 18, 20, 26}` is admissible. -/
