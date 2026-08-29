import Mathlib

/-!
# Config Count Density Of BV
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.configCount_density_of_BV
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

namespace Brockian
namespace EquidistributionBVReduction

open Filter Set MeasureTheory
open scoped Topology

/-- `configCount f x N` is the number of the first `N` points of the sequence `x`, each
configuration `x n` being counted with the weight `f (x n)`. -/

lemma succ_div_mem_Icc {m i : ℕ} (hm : 0 < m) (hi : i < m) :
    (((i : ℝ) + 1) / m) ∈ Icc (0:ℝ) 1 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hi' : (i : ℝ) + 1 ≤ m := by exact_mod_cast hi
  constructor
  · positivity
  · rw [div_le_one hm']; exact hi'

