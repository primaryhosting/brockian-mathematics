/-
# Figalli OT Regularity
Category: Frontier — Fields Medal Work
Target: Frontier.figalli_OT_regularity
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-!
## Setting

We work in the standard Kantorovich-duality framework for optimal transport with a
general cost `c : X → Y → ℝ`.

A pair of potentials `(u, v)` is *admissible* when `u x + v y ≤ c x y` for all `x, y`
(this is the constraint set of the dual Kantorovich problem). The *contact set*
(equivalently, the graph of the `c`-subdifferential of `u`) is the set of pairs where
equality holds; any transport plan that is optimal for `c` is supported in it, and an
optimal transport *map* `T` is precisely a selection of the contact fibers.

The regularity theory of Ma–Trudinger–Wang, Loeper and Figalli (Figalli, Kim, McCann,
Loeper, De Philippis–Figalli) shows that under the MTW condition `(A3w)` together with
suitable convexity of the domains and boundedness of the densities, the `c`-subdifferential
of a `c`-convex Kantorovich potential is *single valued*, i.e. every contact fiber is a
singleton. Below, that single-valuedness is taken as the hypothesis `hT`, and the theorem
`Frontier.figalli_OT_regularity` is the Lean-checked reduction from that hypothesis to
continuity of the optimal transport map: single-valuedness of the contact fibers plus
compactness of the target and continuity of the data force the transport map to be
continuous.

`Frontier.figalli_OT_optimality` records that such a map is indeed an optimal transport
map (it minimises the transport cost among all maps pushing `μ` to `ν`), and
`Frontier.figalli_OT_regularity_example` checks that the hypotheses are non-vacuous on a
genuine quadratic-cost example.
-/

section Contact

variable {X Y : Type*}

/-- Admissible pair of Kantorovich potentials for the cost `c`: the dual constraint
`u x + v y ≤ c x y`. -/

theorem quadCost_contactFiber (x : Set.Icc (0 : ℝ) 1) :
    contactFiber quadCost (fun x => -(x : ℝ)) (fun y => (y : ℝ) - 1 / 2) x = {shiftMap x} := by
  ext y
  simp only [contactFiber, Set.mem_setOf_eq, Set.mem_singleton_iff, quadCost, shiftMap]
  constructor
  · intro h
    have hy : (y : ℝ) = (x : ℝ) + 1 := by nlinarith [sq_nonneg ((y : ℝ) - (x : ℝ) - 1)]
    exact Subtype.ext hy
  · intro h
    have hy : (y : ℝ) = (x : ℝ) + 1 := by rw [h]
    rw [hy]; ring

/-- The optimal transport map of the quadratic-cost example is continuous, as an instance of
`figalli_OT_regularity`. -/
