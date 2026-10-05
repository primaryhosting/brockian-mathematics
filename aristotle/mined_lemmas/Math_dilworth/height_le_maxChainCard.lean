/-
# Dilworth
Category: Pure Mathematics
Target: Math.dilworth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/- -/` rather than `/-! -/` because Lean 4 does not allow a module
-- docstring to precede the `import` commands; the module docstring is repeated below.)

import Mathlib

/-!
# Dilworth
Category: Pure Mathematics
Target: Math.dilworth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Math

open Classical in
/-- The largest cardinality of a chain contained in the finset `t`. -/

lemma height_le_maxChainCard (x : α) : height x ≤ maxChainCard α :=
  chainSup_mono (Finset.filter_subset _ _)

