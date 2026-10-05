/-!
# Singular Series Gaps 9098
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps9098
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This development is deliberately self-contained (it uses no imports at all), so that the
required header comment can literally be the first thing in the file.  Everything below is
built from the Lean 4 core library only.
-/

namespace Brockian

/-! ## Primality, admissible gap patterns -/

/-- Primality, spelled out from first principles: `p` is at least `2` and its only divisors
are `1` and `p`. -/

theorem admissible_gapPattern_fact (k : Nat) : Admissible (gapPattern k (fact k)) := by
  apply SingularSeriesGaps9098
  intro p hp hpk
  exact dvd_fact k p (by have := hp.1; omega) hpk

/-- A concrete new admissible gap range: the `9098`-term progression with common difference
`9098!` is admissible. -/
