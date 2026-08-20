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

lemma tent_eq_zero_right {c d delta x : ℝ} (h : 0 < delta) (h1 : d ≤ x) :
    tent c d delta x = 0 := by
  have h3 : min ((x - c) / delta) ((d - x) / delta) ≤ 0 :=
    le_trans (min_le_right _ _) (div_nonpos_of_nonpos_of_nonneg (by linarith) h.le)
  unfold tent
  rw [max_eq_left h3, min_eq_right zero_le_one]

/-! ## Comparison of the tent integrals with the Sato–Tate measure -/

