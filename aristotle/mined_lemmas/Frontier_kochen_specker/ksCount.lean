import Mathlib

/-!
# Kochen Specker
Category: Frontier Physics
Target: Frontier.kochen_specker
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped InnerProductSpace

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

/-- The four dimensional real Hilbert space in which we work. -/
abbrev KSSpace : Type := EuclideanSpace ℝ (Fin 4)

/-- A vector of `KSSpace` given by its four coordinates. -/

noncomputable def ksCount (v : KSSpace → Bool) (x : KSSpace) : ℕ := if v x = true then 1 else 0

/-- If `v` assigns the value `true` to exactly one member of each orthogonal basis, then the
weights of the four members of an orthogonal basis sum to `1`. -/
