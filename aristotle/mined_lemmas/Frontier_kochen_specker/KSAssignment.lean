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
open scoped RealInnerProductSpace

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

/-- The state space of a single quantum system of (Hilbert space) dimension `4`. -/
abbrev E4 := EuclideanSpace ℝ (Fin 4)

/-- A *noncontextual hidden-variable assignment* (a Kochen–Specker colouring) is a map that
assigns to every unit vector (equivalently, to every rank-one orthogonal projection) a
definite truth value `0`/`1`, in such a way that for every orthonormal basis exactly one
basis vector receives the value `1`.

Note that in dimension `4` an orthonormal family indexed by `Fin 4` is automatically an
orthonormal *basis* (see `Frontier.orthonormal_four_spans`), so the quantification below is
exactly the quantification over all orthonormal bases. -/

def KSAssignment (f : E4 → Bool) : Prop :=
  ∀ v : Fin 4 → E4, Orthonormal ℝ v → ∃! i : Fin 4, f (v i) = true

/-- An orthonormal family of four vectors in a four-dimensional space spans, hence is an
orthonormal basis. -/
