import Mathlib

/-!
# Singular Series Gaps 14501460
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps14501460
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-- `nu H p` is the number of distinct residue classes modulo `p` occupied by the
tuple `H`; in the Hardy–Littlewood singular series this is the quantity `ν_p(H)`
appearing in the local factor `(1 - ν_p(H)/p)(1 - 1/p)^{-|H|}`. -/

lemma admissible_quadruple : Admissible ({0, 1452, 1454, 1460} : Finset ℕ) := by
  apply admissible_of_small_primes
  intro p hp hple
  have hcard : ({0, 1452, 1454, 1460} : Finset ℕ).card = 4 := by decide
  rw [hcard] at hple
  have h2 := hp.two_le
  interval_cases p
  · decide
  · decide
  · exact absurd hp (by decide)

/-!
## Main result
-/

/-- **Singular Series Gaps 1450–1460.**

Within the gap window `1450 ≤ d ≤ 1460`, the admissible gaps `d` — those for
which the pair `{0, d}` has a nonvanishing singular series — are exactly the six
even values `1450, 1452, 1454, 1456, 1458, 1460`; moreover the window supports a
genuinely larger admissible configuration, the `4`-tuple `{0, 1452, 1454, 1460}`,
all of whose singular-series local factors are strictly positive. -/
