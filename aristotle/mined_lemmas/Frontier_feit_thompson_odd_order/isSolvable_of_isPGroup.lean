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

theorem isSolvable_of_isPGroup {p : ℕ} [Fact p.Prime] (G : Type u) [Group G] [Finite G]
    (hp : IsPGroup p G) : IsSolvable G :=
  haveI := hp.isNilpotent
  inferInstance

/-- Base case (unconditional): a finite simple group of prime power order is
commutative, i.e. the simple-group form of Feit–Thompson holds for `p`-groups. -/
