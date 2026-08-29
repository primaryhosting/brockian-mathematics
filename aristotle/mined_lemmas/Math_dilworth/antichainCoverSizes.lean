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

def antichainCoverSizes (α : Type*) [Fintype α] [PartialOrder α] : Set ℕ :=
  {n | ∃ C : Finset (Finset α), C.card ≤ n ∧
      (∀ s ∈ C, IsAntichain (· ≤ ·) (↑s : Set α)) ∧ ∀ x : α, ∃ s ∈ C, x ∈ s}

/-- The height of `x`: the largest size of a chain all of whose elements are `≤ x`. -/
