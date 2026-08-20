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

/-- The one-loop coefficient `b₀` of the beta function of an `SU(N)` gauge theory
coupled to `Nf` Dirac fermions in the fundamental representation:
`b₀ = 11/3 * N - 2/3 * Nf`. -/

noncomputable def betaOneLoop (N Nf : ℕ) (g : ℝ) : ℝ :=
  - b0 N Nf * g ^ 3 / (16 * Real.pi ^ 2)

/-- The one-loop coefficient `b₀` is positive precisely in the asymptotically free regime
`2 Nf < 11 N`. -/
