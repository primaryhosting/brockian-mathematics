import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian

/-- A finite set `H` of integers is *admissible* if for every prime `p` it fails to cover
all residue classes modulo `p`, i.e. some residue class mod `p` is missed by `H`.
This is the classical admissibility condition of the Hardy–Littlewood prime `k`-tuple
conjecture. -/

lemma singularFactor_pos (d : ℕ) : 0 < singularFactor d := by
  refine Finset.prod_pos ?_
  intro p hp
  have hp2 : p ≠ 2 := Finset.ne_of_mem_erase hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)
  have h3 : 3 ≤ p := by have := hpp.two_le; omega
  have h3' : (3 : ℚ) ≤ (p : ℚ) := by exact_mod_cast h3
  apply div_pos <;> linarith

/-- The singular series of an even gap is positive. -/
