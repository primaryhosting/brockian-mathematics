import Mathlib

/-!
# Mordell Finite Generation
Category: Frontier — Prime Numbers
Target: Frontier.Mordell_finite_generation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

/-- **Descent theorem** (the group-theoretic heart of the Mordell–Weil theorem).

Let `A` be an abelian group equipped with a real-valued "height" function `h` such that

* `hfin`  : every sublevel set `{P | h P ≤ C}` is finite;
* `htrans`: translation by a fixed element at worst doubles the height, up to a constant;
* `hdup`  : duplication at least quadruples the height, up to a constant;
* `hweak` : (weak Mordell–Weil) `A / 2A` is finite, phrased as the existence of a finite set
            of coset representatives `S` for the subgroup `2A`.

Then `A` is a finitely generated abelian group. -/

theorem to the theory of heights and to weak Mordell–Weil. -/
