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

def trivialCG : ConstraintGraph :=
  { numV := 1, alphSize := 1, numE := 0, ends := Fin.elim0, ok := Fin.elim0 }

/-- A single variable with a single, always violated, constraint: `UNSAT = 1`. -/
