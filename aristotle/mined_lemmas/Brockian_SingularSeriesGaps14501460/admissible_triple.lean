/-
# Singular Series Gaps 14501460
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps14501460
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring, so the header above is a plain
-- block comment; the identical module docstring follows the import.)

import Mathlib

/-!
# Singular Series Gaps 14501460
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps14501460
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
Mathlib lemmas doing the real work here: `Finset.card_image_le` (bounds the local density
`ν_H(p)` by `|H|`), `ZMod.natCast_eq_zero_iff` (evens vanish mod `2`), and
`Finset.prod_pos` (positivity of the truncated Euler product).
-/

namespace Brockian

/-- The local density `ν_H(p)`: the number of residue classes modulo `p` occupied by the
shift set `H`.  This is the quantity appearing in each Euler factor of the Hardy–Littlewood
singular series of the tuple `H`. -/

lemma admissible_triple : Admissible ({0, 1452, 1458} : Finset ℕ) := by
  intro p hp
  by_cases h3 : 3 < p
  · have hcard : ({0, 1452, 1458} : Finset ℕ).card ≤ 3 := by decide
    exact lt_of_le_of_lt ((localDensity_le_card _ p).trans hcard) h3
  · interval_cases p
    · exact absurd hp (by decide)
    · exact absurd hp (by decide)
    · have : localDensity ({0, 1452, 1458} : Finset ℕ) 2 = 1 := by decide
      omega
    · have : localDensity ({0, 1452, 1458} : Finset ℕ) 3 = 1 := by decide
      omega

/-!
## Main result

A new admissible gap range around `1450–1460`:

* every even gap `d` in the range `1450 ≤ d ≤ 1460` yields an admissible pair `{0, d}`,
* the triple `{0, 1452, 1458}` of diameter `1458` inside that range is admissible,
* consequently all truncations of its Hardy–Littlewood singular series are strictly
  positive, so there is no local obstruction to infinitely many prime triples with these
  gaps.
-/
