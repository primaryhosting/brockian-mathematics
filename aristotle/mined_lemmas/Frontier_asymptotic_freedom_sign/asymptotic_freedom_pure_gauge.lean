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

/-- The one-loop coefficient `b₀` of the SU(N) gauge beta function with `nf` Dirac
fermion flavours in the fundamental representation:
`b₀ = 11 N / 3 - 2 nf / 3`. -/

theorem asymptotic_freedom_pure_gauge (N : ℕ) (hN : 1 ≤ N) (g : ℝ) (hg : 0 < g) :
    betaOneLoop N 0 g < 0 :=
  asymptotic_freedom_sign N 0 g hg (by omega)

end Frontier

