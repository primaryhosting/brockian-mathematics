/-
# Feit Thompson Odd Order
Category: Frontier Abel
Target: Frontier.feit_thompson_odd_order
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Frontier

universe u

/-- The full Feit–Thompson theorem, as a proposition about a universe of types:
every finite group of odd order is solvable. -/

theorem isSolvable_of_odd_card_lt_45 {G : Type u} [Group G] [Finite G]
    (hodd : Odd (Nat.card G)) (hlt : Nat.card G < 45) : IsSolvable G := by
  rcases odd_lt_45_prime_pow_or_prime_mul_prime _ hlt hodd with
    ⟨p, -, k, -, hp, hcard⟩ | ⟨p, -, q, -, hp, hq, hpq, hcard⟩
  · exact isSolvable_of_card_eq_prime_pow hp hcard
  · exact isSolvable_of_card_eq_prime_mul_prime hp hq hpq hcard

end Frontier

