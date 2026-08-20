/-
# Feit Thompson Odd Order
Category: Frontier Abel
Target: Frontier.feit_thompson_odd_order
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to precede any module docstring, so the header above is
-- repeated verbatim as the module docstring immediately after the import.)
import Mathlib

/-!
# Feit Thompson Odd Order
Category: Frontier Abel
Target: Frontier.feit_thompson_odd_order
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

universe u

namespace Frontier

/-- Every divisor of an odd natural number is odd. -/

theorem comm_of_isPGroup_of_isSimpleGroup {p : ℕ} [Fact p.Prime] (G : Type u) [Group G] [Finite G]
    (hp : IsPGroup p G) [IsSimpleGroup G] (a b : G) : a * b = b * a :=
  haveI := hp.isNilpotent
  IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance a b

/-- Base case (unconditional): a finite group of odd order at most `3` is solvable. -/
