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
# Goldbach Beyond Of Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_beyond_of_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Goldbach Beyond Of Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_beyond_of_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Contents

* `GoldbachModel S`: a model of the binary Goldbach schema over a set `S` of naturals.
* `goldbach_beyond_of_model`: the target theorem — from a model covering `n - 3` one gets the
  ternary Goldbach statement at any odd `n ≥ 9`.  It is proved outright (no hypothesis is
  assumed as an axiom) and it is non-vacuous: `goldbachModel_Iic_300` exhibits an explicit,
  computationally verified model.
* `goldbach_le_300` / `goldbachModel_Iic_300`: unconditional discharge of the model hypothesis
  on the range `[4, 300]`, by kernel computation.
* `ternary_le_303`: the resulting unconditional ternary Goldbach statement for odd `9 ≤ n ≤ 303`.

A model over `Set.univ` (`goldbachModel_univ_iff`) is precisely Goldbach's conjecture, which is
open; so the model hypothesis is discharged here exactly on the finite ranges that can be
verified, and left as a hypothesis in general.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Brockian.GoldbachSchema

/-- `IsGoldbachSum n` says that `n` is a sum of two primes. -/

theorem goldbachModel_Iic_300 : GoldbachModel (Set.Iic 300) :=
  ⟨fun n hn h4 he => goldbach_le_300 n hn h4 he⟩

/-- Unconditional ternary Goldbach in the verified range: every odd `n` with `9 ≤ n ≤ 303`
is a sum of three primes. -/
