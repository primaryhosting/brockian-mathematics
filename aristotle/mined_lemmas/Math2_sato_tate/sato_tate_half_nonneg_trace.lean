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

open Filter Topology Set MeasureTheory intervalIntegral
open scoped Real

namespace Math2

/-- The Sato–Tate density on `[0, π]`: `θ ↦ (2/π) sin²θ`. -/

theorem sato_tate_half_nonneg_trace (a : ℕ → ℤ)
    (hST : SatoTateEquidistributed fun p => frobeniusAngle p (a p)) :
    Tendsto (fun X : ℕ => ((((primesBelow X).filter fun p => 0 ≤ a p).card : ℝ))
        / (primesBelow X).card)
      atTop (𝓝 (1 / 2)) := by
  have hpi := Real.pi_pos
  have h := satoTate_interval hST (α := 0) (β := Real.pi / 2) le_rfl (by linarith) (by linarith)
  rw [integral_satoTateDensity_half] at h
  refine h.congr fun X => ?_
  have hfil : ((primesBelow X).filter fun p => frobeniusAngle p (a p) ∈ Icc 0 (Real.pi / 2))
      = ((primesBelow X).filter fun p => 0 ≤ a p) := by
    refine Finset.filter_congr fun p hp => ?_
    have hp' : 0 < p := (Finset.mem_filter.1 hp).2.pos
    exact frobeniusAngle_mem_Icc_half hp' (a p)
  rw [hfil]

#print axioms Math2.sato_tate
#print axioms Math2.satoTate_iff_intervals
#print axioms Math2.sato_tate_half_nonneg_trace

end Math2

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

