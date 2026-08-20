/-
# Chebotarev
Category: Frontier Math
Target: Math2.chebotarev
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Chebotarev
Category: Frontier Math
Target: Math2.chebotarev
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

open ArithmeticFunction Complex Filter Topology

/-! ### The analytic input: Λ-weighted density of a residue class -/

/-- The terms of the `L`-series of the von Mangoldt function restricted to a residue class,
evaluated at a real point, are real. -/

theorem tendsto_aux_re (q : ℕ) [NeZero q] (a : ZMod q) :
    Tendsto (fun s : ℝ => (vonMangoldt.LFunctionResidueClassAux a (s : ℂ)).re) (𝓝[>] (1 : ℝ))
      (𝓝 ((vonMangoldt.LFunctionResidueClassAux a 1).re)) := by
  have hc : ContinuousWithinAt (vonMangoldt.LFunctionResidueClassAux a) {s : ℂ | 1 ≤ s.re} 1 :=
    vonMangoldt.continuousOn_LFunctionResidueClassAux a 1 (by simp)
  have h1 : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝[{s : ℂ | 1 ≤ s.re}] 1) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · simpa using (Complex.continuous_ofReal.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simpa using le_of_lt hs
  exact Complex.continuous_re.continuousAt.tendsto.comp (hc.tendsto.comp h1)

