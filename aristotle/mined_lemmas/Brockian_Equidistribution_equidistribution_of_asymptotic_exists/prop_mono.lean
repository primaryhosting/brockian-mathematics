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
# Equidistribution Of Asymptotic Exists
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

open Filter Topology

set_option maxHeartbeats 1000000

namespace Brockian.Equidistribution

/-- `countBelow x N a` is the number of indices `n < N` whose fractional part
`Int.fract (x n)` is smaller than `a`. -/

lemma prop_mono (x : ℕ → ℝ) (N : ℕ) {a b : ℝ} (hab : a ≤ b) :
    prop x N a ≤ prop x N b := by
  refine div_le_div_of_nonneg_right ?_ ?_ |>.trans_eq rfl
  · exact_mod_cast countBelow_mono x N hab
  · exact Nat.cast_nonneg _

/-- **Equidistribution from asymptotics on a dense set of thresholds.**

Let `x : ℕ → ℝ` be a sequence and let `D` be a set of thresholds that is dense in the
unit interval (between any two points of `[0,1]` there is a point of `D`).  Assume that
for every threshold `a ∈ D` the asymptotic proportion of terms with fractional part below
`a` exists and equals `a`.  Then the sequence is equidistributed modulo one: for *every*
`a ∈ [0,1]` the asymptotic proportion exists and equals `a`. -/
