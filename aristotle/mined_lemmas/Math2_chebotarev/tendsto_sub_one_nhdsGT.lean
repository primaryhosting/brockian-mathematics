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

theorem tendsto_sub_one_nhdsGT : Tendsto (fun s : ℝ => s - 1) (𝓝[>] (1 : ℝ)) (𝓝 0) := by
  have h : Tendsto (fun s : ℝ => s - 1) (𝓝 (1 : ℝ)) (𝓝 ((1 : ℝ) - 1)) :=
    (continuous_id.tendsto (1 : ℝ)).sub_const 1
  simpa using h.mono_left nhdsWithin_le_nhds

/-- **Dirichlet density of a residue class** (von Mangoldt weighted form). -/
