/-
# Dilworth
Category: Pure Mathematics
Target: Math.dilworth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring, so the required header is
-- reproduced verbatim as a module docstring immediately after the import below.)

import Mathlib

/-!
# Dilworth
Category: Pure Mathematics
Target: Math.dilworth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Classical

namespace Math

variable {α : Type*} [Fintype α] [PartialOrder α]

/-- The length of a longest chain in a finite poset. -/

lemma level_isAntichain (i : ℕ) : IsAntichain (· ≤ ·) (↑(level α i) : Set α) := by
  intro x hx y hy hne hxy
  simp only [level, Set.mem_toFinset, Finset.mem_coe, Set.mem_setOf_eq] at hx hy
  have : height x < height y := height_strictMono (lt_of_le_of_ne hxy hne)
  omega

