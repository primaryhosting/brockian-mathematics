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

lemma div_le_succ_div {m i : ℕ} (hm : 0 < m) : (i : ℝ) / m ≤ ((i : ℝ) + 1) / m := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have h : ((i : ℝ) + 1) / m - (i : ℝ) / m = 1 / m := by field_simp; ring
  have h2 : (0 : ℝ) < 1 / m := by positivity
  linarith

/-- Splitting the first `N` points according to which of the `m` intervals `[i/m, (i+1)/m)`
they belong to. -/
