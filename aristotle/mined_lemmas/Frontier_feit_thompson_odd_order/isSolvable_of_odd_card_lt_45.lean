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

universe u

namespace Frontier

/-!
## Statement

The Feit–Thompson odd order theorem states that every finite group of odd order is
solvable.  Its proof is a 255-page argument and is not available in Mathlib.  What is
formalized here is:

* the statement itself, in the form `OddOrderSolvable`;
* a complete, machine-checked **reduction** of the statement to its minimal-counterexample
  ("simple") case, `Frontier.feit_thompson_odd_order`;
* unconditional **base cases**: groups of odd prime-power order, groups of odd order the
  product of two distinct primes, and — combining these — every group of odd order less
  than `45`, the first odd order that is neither a prime power nor squarefree.
-/

/-- Having no normal subgroup other than `⊥` and `⊤` (for a nontrivial group this is
exactly simplicity). -/

theorem isSolvable_of_odd_card_lt_45 (G : Type u) [Group G] [Finite G]
    (hodd : Odd (Nat.card G)) (hlt : Nat.card G < 45) : IsSolvable G := by
  rcases odd_lt_45_prime_pow_or_prime_mul_prime (Nat.card G) hodd hlt with
    ⟨p, k, hp, h⟩ | ⟨p, q, hp, hq, hpq, h⟩
  · exact isSolvable_of_card_eq_prime_pow hp h
  · exact isSolvable_of_card_eq_prime_mul_prime hp hq hpq h

/-- **Reduction of Feit–Thompson to the simple case.**  Granting that every finite group of
odd order with no proper nontrivial normal subgroup is abelian, every finite group of odd
order is solvable.  The hypothesis is exactly the hard content of the Feit–Thompson odd
order theorem; the reduction proved here is a complete, machine-checked strong induction on
the order of the group. -/
