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

/-
# Pcp Dinur
Category: Frontier Cs
Target: CS.pcp_dinur
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Dinur's gap amplification and the PCP theorem (statement)

We formalise binary constraint satisfaction instances (`CS.ConstraintGraph`) together with their
`UNSAT` value, and prove the outer, iterative structure of Dinur's proof of the PCP theorem
(`CS.pcp_dinur`): from a single gap-amplification step — preserving perfect completeness,
doubling the `UNSAT` value up to a constant threshold, and increasing the size by at most a
constant factor — iterating logarithmically many times yields a reduction with a constant gap
and polynomial size blowup.  We also check that these hypotheses are not vacuous
(`CS.pcp_dinur_hypotheses_nonvacuous`).
-/

set_option autoImplicit false

namespace CS

/-- A finite constraint graph (a binary constraint satisfaction instance): `numE` constraints,
each attached to an ordered pair of the `numV` variables, each variable taking values in an
alphabet of size `alphSize`, and each constraint given by a decidable binary relation. -/
structure ConstraintGraph where
  /-- number of variables -/
  numV : ℕ
  /-- size of the alphabet -/
  alphSize : ℕ
  /-- number of constraints -/
  numE : ℕ
  /-- the pair of variables each constraint acts on -/
  ends : Fin numE → Fin numV × Fin numV
  /-- the constraint relation attached to each edge -/
  ok : Fin numE → Fin alphSize → Fin alphSize → Bool

/-- The fraction of constraints of `G` violated by the assignment `a`. -/

theorem numE_iterate_le {T : ConstraintGraph → ConstraintGraph} {C : ℕ}
    (hsize : ∀ H : ConstraintGraph, (T H).numE ≤ C * H.numE) (G : ConstraintGraph) :
    ∀ k : ℕ, (T^[k] G).numE ≤ C ^ k * G.numE := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      calc (T (T^[k] G)).numE ≤ C * (T^[k] G).numE := hsize _
        _ ≤ C * (C ^ k * G.numE) := by
              exact Nat.mul_le_mul_left C ih
        _ = C ^ (k + 1) * G.numE := by ring

/--
**Dinur's gap amplification and the PCP theorem (statement).**

Assume we are given Dinur's gap-amplification step: a transformation `T` of constraint graphs
(over a fixed alphabet) which

* preserves perfect completeness (`hcomplete`: satisfiable instances stay satisfiable),
* doubles the `UNSAT` value up to a constant threshold `alpha`
  (`hamp`: `unsat (T H) ≥ min (2 * unsat H) alpha`),
* and blows up the size by at most a constant factor `C` (`hsize`).

Then for every unsatisfiable instance `G` there is a number of iterations `k` such that the
composed reduction `T^[k]`

* still maps satisfiable instances to satisfiable instances,
* maps `G` to an instance with constant gap `unsat (T^[k] G) ≥ alpha`,
* increases the size by at most a factor `C ^ k`,
* with `k` logarithmic in `1 / unsat G` (i.e. `2 ^ k ≤ max 1 (2 * alpha / unsat G)`), so that
  the total size blowup `C ^ k` is polynomial.

This is exactly the outer structure of Dinur's proof of the PCP theorem: iterating the
gap-amplification lemma `O(log n)` times turns a decision problem into a constant-gap
constraint satisfaction problem with only a polynomial increase in size.
-/
