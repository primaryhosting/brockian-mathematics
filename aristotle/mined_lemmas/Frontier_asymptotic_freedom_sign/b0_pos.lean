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

theorem b0_pos {N Nf : ℕ} (h : 2 * Nf < 11 * N) : 0 < b0 N Nf := by
  have h' : (2 : ℝ) * (Nf : ℝ) < 11 * (N : ℝ) := by
    exact_mod_cast (by exact_mod_cast h : ((2 * Nf : ℕ) : ℝ) < ((11 * N : ℕ) : ℝ))
  unfold b0
  linarith

/-- **Asymptotic freedom (sign of the one-loop beta function).**
For an `SU(N)` gauge theory with `Nf` fundamental Dirac fermions satisfying `2 Nf < 11 N`
(in particular for pure `SU(N)` Yang–Mills, `Nf = 0`, `N ≥ 1`), the one-loop beta function
is strictly negative at any positive coupling `g`. -/
