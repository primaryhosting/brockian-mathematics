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

theorem isSolvable_of_card_eq_prime_mul_prime {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p ≠ q) (h : Nat.card G = p * q) : IsSolvable G := by
  have hsf : Squarefree (Nat.card G) := by
    rw [h, Nat.squarefree_mul ((Nat.coprime_primes hp hq).mpr hpq)]
    exact ⟨hp.squarefree, hq.squarefree⟩
  haveI : IsZGroup G := IsZGroup.of_squarefree hsf
  infer_instance

end Aux

/-- Every odd number below `45` is either a prime power or a product of two distinct
primes.  (`45 = 3 ^ 2 * 5` is the least odd number that is neither.) -/
