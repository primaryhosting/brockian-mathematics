/-
# Cos Trace Norm 2707
Category: Brockian Corpus
Target: Brockian.CosTraceNorm2707
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Brockian

/-- The larger eigenvalue of the real symmetric matrix `!![a, b; b, d]`. -/

theorem eig_isRoot (a b d x : ℝ) (hx : x = eigTop a b d ∨ x = eigBot a b d) :
    x ^ 2 - (a + d) * x + (a * d - b ^ 2) = 0 := by
  have hnn : (0:ℝ) ≤ (a - d) ^ 2 + 4 * b ^ 2 := by positivity
  have hs : Real.sqrt ((a - d) ^ 2 + 4 * b ^ 2) ^ 2 = (a - d) ^ 2 + 4 * b ^ 2 :=
    Real.sq_sqrt hnn
  rcases hx with h | h <;> subst h <;>
    · simp only [eigTop, eigBot]
      nlinarith [hs]

/-- Sum of the two eigenvalues is the trace. -/
