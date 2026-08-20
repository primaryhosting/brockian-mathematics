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

theorem asymptotic_freedom_sign {N Nf : ℕ} (h : 2 * Nf < 11 * N) {g : ℝ} (hg : 0 < g) :
    betaOneLoop N Nf g < 0 := by
  have hb : 0 < b0 N Nf := b0_pos h
  have hg3 : 0 < g ^ 3 := pow_pos hg 3
  have hpi : 0 < 16 * Real.pi ^ 2 := by positivity
  unfold betaOneLoop
  apply div_neg_of_neg_of_pos _ hpi
  nlinarith

/-- Base case: pure `SU(3)` Yang–Mills (no fermions) is asymptotically free. -/
