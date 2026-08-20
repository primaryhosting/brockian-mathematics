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

theorem tendsto_residueClass_density (q : ℕ) [NeZero q] {a : ZMod q} (ha : IsUnit a) :
    Tendsto (fun s : ℝ => (s - 1) * ∑' n : ℕ, vonMangoldt.residueClass a n / (n : ℝ) ^ s)
      (𝓝[>] (1 : ℝ)) (𝓝 ((q.totient : ℝ)⁻¹)) := by
  have h0 : Tendsto (fun s : ℝ => (s - 1) *
      (vonMangoldt.LFunctionResidueClassAux a (s : ℂ)).re + (q.totient : ℝ)⁻¹)
      (𝓝[>] (1 : ℝ)) (𝓝 ((q.totient : ℝ)⁻¹)) := by
    have h1 : Tendsto (fun s : ℝ => s - 1) (𝓝[>] (1 : ℝ)) (𝓝 0) :=
      tendsto_sub_one_nhdsGT
    simpa using ((h1.mul (tendsto_aux_re q a)).add_const ((q.totient : ℝ)⁻¹))
  refine h0.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : (1 : ℝ) < s := hs
  have hne : s - 1 ≠ 0 := by linarith
  have hc : (s - 1) * ((q.totient : ℝ)⁻¹ / (s - 1)) = (q.totient : ℝ)⁻¹ := by
    field_simp
  rw [tsum_residueClass_rpow_eq q ha s hs', mul_add, hc]

/-! ### Restricting to primes -/

/-- For `s ≥ 1`, the terms over non-primes are dominated by the corresponding terms at `s = 1`. -/
