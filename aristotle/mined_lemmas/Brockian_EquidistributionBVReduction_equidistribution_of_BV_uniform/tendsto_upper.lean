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
# Equidistribution Of BV Uniform
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.equidistribution_of_BV_uniform
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Equidistribution Of BV Uniform
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.equidistribution_of_BV_uniform
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

set_option grind.warning false

namespace Brockian.EquidistributionBVReduction

open Filter Finset

/-- `countBelow x N a` is the number of indices `n < N` whose fractional part is `< a`. -/

lemma tendsto_upper (x : ℕ → ℝ) (hx : UniformlyDistributedMod1 x) (g : ℝ → ℝ) (k : ℕ)
    (hk : 0 < k) :
    Tendsto (fun N => ∑ j ∈ Finset.range k,
        g (((j:ℝ)+1)/k) * (edf x N (((j:ℝ)+1)/k) - edf x N ((j:ℝ)/k))) atTop
      (nhds (∑ j ∈ Finset.range k, g (((j:ℝ)+1)/k) / k)) := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  refine tendsto_finset_sum _ ?_
  intro j hj
  simp only [Finset.mem_range] at hj
  have h1 : ((j:ℝ)+1)/k ∈ Set.Icc (0:ℝ) 1 := by
    have h := pt_mem k (j+1) hk hj
    rwa [show ((j+1:ℕ):ℝ)/k = ((j:ℝ)+1)/k by push_cast; ring] at h
  have h2 : ((j:ℝ)/k) ∈ Set.Icc (0:ℝ) 1 := pt_mem k j hk (by omega)
  have hconv := ((hx _ h1).sub (hx _ h2)).const_mul (g (((j:ℝ)+1)/k))
  have heq : g (((j:ℝ)+1)/k) * (((j:ℝ)+1)/k - (j:ℝ)/k) = g (((j:ℝ)+1)/k) / k := by
    field_simp
    ring
  rwa [heq] at hconv

/-- Convergence of the lower bin sums. -/
