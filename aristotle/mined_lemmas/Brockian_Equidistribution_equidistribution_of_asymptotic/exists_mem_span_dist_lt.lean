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

/-
# Equidistribution Of Asymptotic
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Equidistribution Of Asymptotic
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Filter Topology AddCircle

namespace Brockian.Equidistribution

/-- The Cesàro (Birkhoff) average of `f` along the first `N` terms of the sequence `x`. -/

lemma exists_mem_span_dist_lt (f : C(AddCircle (1 : ℝ), ℂ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ g ∈ Submodule.span ℂ (Set.range (fourier (T := 1))), dist f g < ε := by
  have hf : f ∈ closure ((Submodule.span ℂ (Set.range (fourier (T := 1)))) : Set _) := by
    rw [← Submodule.topologicalClosure_coe, span_fourier_closure_eq_top]
    trivial
  exact (Metric.mem_closure_iff.mp hf) ε hε

/-- **Weyl's equidistribution criterion.**  If the exponential sums
`(1/N) ∑_{n < N} e(k xₙ)` tend to `0` for every nonzero integer frequency `k`, then the
sequence `x` is equidistributed in the circle `ℝ/ℤ`: the Cesàro averages of every continuous
function converge to its integral against the Haar probability measure. -/
