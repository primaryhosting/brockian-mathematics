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

/-- The posterior probability that an agent with information partition `cell`
assigns to the event `E` at the state `ω`, under the prior weights `p`:
it is `p (E ∩ cell ω) / p (cell ω)`. -/

noncomputable def posterior {Ω : Type*} [DecidableEq Ω]
    (p : Ω → ℝ) (E : Finset Ω) (cell : Ω → Finset Ω) (ω : Ω) : ℝ :=
  (∑ y ∈ cell ω ∩ E, p y) / (∑ y ∈ cell ω, p y)

/-- If an event `M` is a union of cells of the partition `cell`, and the posterior of
`E` is constantly `q` on `M`, then `p (E ∩ M) = q * p M`. -/
