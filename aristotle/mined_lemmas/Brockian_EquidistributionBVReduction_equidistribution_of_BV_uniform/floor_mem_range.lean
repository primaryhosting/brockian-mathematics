import Mathlib
import RequestProject.Brockian.EquidistributionBVReduction

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
# Equidistribution Of BV Uniform
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.equidistribution_of_BV_uniform
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Finset Set
open scoped Topology BigOperators Classical

set_option maxHeartbeats 1000000

namespace Brockian
namespace EquidistributionBVReduction

/-- `countIn x a b N` is the number of indices `n < N` with `x n ∈ [a, b)`. -/

lemma floor_mem_range (hx : ∀ n, x n ∈ Set.Ico (0 : ℝ) 1) (hk : 0 < k) (N : ℕ) :
    ∀ n ∈ Finset.range N, ⌊(k : ℝ) * x n⌋₊ ∈ Finset.range k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  intro n _
  simp only [Finset.mem_range]
  have h1 : (k : ℝ) * x n < k := by nlinarith [(hx n).1, (hx n).2]
  exact_mod_cast (Nat.floor_lt (mul_nonneg hk'.le (hx n).1)).2 (by exact_mod_cast h1)

/-- Upper bound of the sum of a monotone function along the sequence by the upper Darboux
sum weighted with the counting function. -/
