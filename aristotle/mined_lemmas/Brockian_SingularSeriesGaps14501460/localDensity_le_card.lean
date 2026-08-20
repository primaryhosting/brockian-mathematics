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

lemma localDensity_le_card (H : Finset ℕ) (p : ℕ) : localDensity H p ≤ H.card :=
  Finset.card_image_le

