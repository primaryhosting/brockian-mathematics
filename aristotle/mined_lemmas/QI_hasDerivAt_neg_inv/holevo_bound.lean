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
# Scalar integrals used in the integral representations
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace QI


theorem holevo_bound (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (hρ : ∀ x, (ρ x).PosDef) (hρ1 : ∀ x, (ρ x).trace = 1) (hE : IsPOVM E) :
    mutualInformation (measureDist p ρ E) ≤ holevoChi p ρ := by
  have hbar : (ensembleAvg p ρ).PosDef := ensembleAvg_posDef hp0 hp1 hρ
  have hbartr : (ensembleAvg p ρ).trace = 1 := ensembleAvg_trace hp1 (fun x => hρ1 x)
  rw [mutualInformation_eq_sum hp0 hρ hρ1 hE, holevoChi_eq_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  refine mul_le_mul_of_nonneg_left ?_ (hp0 x)
  exact relEntropy_measurement (hρ x) hbar (by rw [hρ1 x, hbartr]) hE

/-- **The Holevo bound for the accessible information.**  The accessible information of an
ensemble of faithful quantum states, measured with POVMs having outcomes in a fixed finite set,
is at most the Holevo quantity of the ensemble. -/
