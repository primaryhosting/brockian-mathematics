/-
# Sumset Lower Bound
Category: Frontier Wave 2 (deeper machinery)
Target: AdditiveComb.sumset_lower_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- NOTE: Lean 4 requires `import` commands to precede every other command, including module
-- docstrings (`/-! ... -/`). The requested header is therefore reproduced verbatim above as an
-- ordinary block comment (`/- ... -/`), which is legal before `import`, and again as the module
-- docstring below, so that the file actually compiles.

import Mathlib

/-!
# Sumset Lower Bound
Category: Frontier Wave 2 (deeper machinery)
Target: AdditiveComb.sumset_lower_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Pointwise

namespace AdditiveComb

/-- **Sumset lower bound over the integers** (the Cauchy–Davenport analogue over `ℤ`, i.e.
Freiman's lemma base case): for nonempty finite sets `A B : Finset ℤ`,
`|A| + |B| - 1 ≤ |A + B|`, where the subtraction is truncated natural subtraction.

The proof cites Mathlib's `cauchy_davenport_add_of_linearOrder_isCancelAdd`, the Cauchy–Davenport

theorem for linearly ordered additive cancellative semigroups. -/
