import Brockian.GoldbachSchema

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

import Mathlib

/-!
# Goldbach Beyond Of Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_beyond_of_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxRecDepth 100000

namespace Brockian
namespace GoldbachSchema

/-- The Goldbach property: `n` is a sum of two primes. -/

theorem goldbach_beyond_infinite :
    {n : ℕ | Even n ∧ IsStrongGoldbach n}.Infinite := by
  refine Set.infinite_of_forall_exists_gt ?_
  intro a
  obtain ⟨n, hlt, heven, hgold⟩ := goldbach_beyond_of_model a
  exact ⟨n, ⟨heven, hgold⟩, hlt⟩

/-- Base of the schema: the Goldbach property is verified for every even `n` with
`4 ≤ n ≤ 100`. -/
