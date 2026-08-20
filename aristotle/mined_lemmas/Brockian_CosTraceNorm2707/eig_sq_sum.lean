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

theorem eig_sq_sum (a b d : ℝ) :
    eigTop a b d ^ 2 + eigBot a b d ^ 2 = a ^ 2 + 2 * b ^ 2 + d ^ 2 := by
  have hnn : (0:ℝ) ≤ (a - d) ^ 2 + 4 * b ^ 2 := by positivity
  have hs : Real.sqrt ((a - d) ^ 2 + 4 * b ^ 2) ^ 2 = (a - d) ^ 2 + 4 * b ^ 2 :=
    Real.sq_sqrt hnn
  simp only [eigTop, eigBot]
  nlinarith [hs]

/-- Elementary `ℓ¹`–`ℓ²` bound in two dimensions. -/
