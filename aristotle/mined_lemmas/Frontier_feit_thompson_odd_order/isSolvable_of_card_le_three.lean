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

theorem isSolvable_of_card_le_three (G : Type u) [Group G] [Finite G]
    (hodd : Odd (Nat.card G)) (hle : Nat.card G ≤ 3) : IsSolvable G := by
  have hpos : 0 < Nat.card G := Nat.card_pos
  have hcard : Nat.card G = 1 ∨ Nat.card G = 3 := by
    rw [Nat.odd_iff] at hodd; omega
  rcases hcard with h | h
  · haveI : Subsingleton G := Nat.card_eq_one_iff_unique.mp h |>.1
    infer_instance
  · haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    haveI : IsCyclic G := isCyclic_of_prime_card (p := 3) h
    infer_instance

end Frontier

import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

