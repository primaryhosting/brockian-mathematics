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

noncomputable def chainSup {α : Type*} [PartialOrder α] (t : Finset α) : ℕ :=
  t.powerset.sup fun s : Finset α => if IsChain (· ≤ ·) (↑s : Set α) then s.card else 0

/-- The length of a longest chain in the finite poset `α`. -/
