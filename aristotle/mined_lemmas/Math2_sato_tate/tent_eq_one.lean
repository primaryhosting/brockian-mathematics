/-
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Math2

open Filter Topology

/-! ## The Sato–Tate measure -/

/-- The density of the Sato–Tate measure `(2/π) sin²θ dθ` on `[0, π]`. -/

lemma tent_eq_one {c d delta x : ℝ} (h : 0 < delta) (h1 : c + delta ≤ x) (h2 : x ≤ d - delta) :
    tent c d delta x = 1 := by
  have h3 : 1 ≤ min ((x - c) / delta) ((d - x) / delta) :=
    le_min (by rw [le_div_iff₀ h]; linarith) (by rw [le_div_iff₀ h]; linarith)
  unfold tent
  rw [max_eq_right (le_trans zero_le_one h3), min_eq_left h3]

