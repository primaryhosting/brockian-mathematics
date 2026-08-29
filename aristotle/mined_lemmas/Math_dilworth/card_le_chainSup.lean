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

lemma card_le_chainSup {t s : Finset α}
    (hs : s ⊆ t) (hc : IsChain (· ≤ ·) (↑s : Set α)) : s.card ≤ chainSup t := by
  classical
  have h : s ∈ t.powerset := Finset.mem_powerset.mpr hs
  have := Finset.le_sup
    (f := fun s : Finset α => if IsChain (· ≤ ·) (↑s : Set α) then s.card else 0) h
  simpa [chainSup, hc] using this

