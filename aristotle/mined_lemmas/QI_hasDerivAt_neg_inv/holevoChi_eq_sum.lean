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


theorem holevoChi_eq_sum :
    holevoChi p ρ = ∑ x, p x * relEntropy (ρ x) (ensembleAvg p ρ) := by
  have hlin : (ensembleAvg p ρ * logM (ensembleAvg p ρ)).trace.re
      = ∑ x, p x * (ρ x * logM (ensembleAvg p ρ)).trace.re :=
    trace_sum_smul_mul _ _ _
  have hrhs : ∑ x, p x * relEntropy (ρ x) (ensembleAvg p ρ)
      = (∑ x, p x * (ρ x * logM (ρ x)).trace.re)
        - ∑ x, p x * (ρ x * logM (ensembleAvg p ρ)).trace.re := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => by rw [relEntropy]; ring
  rw [hrhs, holevoChi, vnEntropy, hlin]
  simp only [vnEntropy, mul_neg, Finset.sum_neg_distrib]
  ring

/-- The mutual information of the measurement statistics is the average Kullback-Leibler
divergence of the conditional outcome distributions from the average one. -/
