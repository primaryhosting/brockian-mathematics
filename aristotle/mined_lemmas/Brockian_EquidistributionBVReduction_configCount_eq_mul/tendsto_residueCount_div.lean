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
# Config Count Over Main Tendsto
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.configCount_over_main_tendsto
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Classical

open Filter Finset

namespace Brockian.EquidistributionBVReduction

/-- The number of `n < N` lying in the residue class `r` modulo `q`. -/

lemma tendsto_residueCount_div (q r : ℕ) (hq : 0 < q) :
    Tendsto (fun N : ℕ => (residueCount q r N : ℝ) / ((N : ℝ) / q)) atTop (nhds 1) := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hbound : ∀ᶠ N : ℕ in atTop,
      ‖(residueCount q r N : ℝ) / ((N : ℝ) / q) - 1‖ ≤ (q : ℝ) / N := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have key : (residueCount q r N : ℝ) / ((N : ℝ) / q) - 1
        = ((residueCount q r N : ℝ) - (N : ℝ) / q) / ((N : ℝ) / q) := by
      field_simp
    rw [key, norm_div, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (show (0:ℝ) < (N : ℝ) / q by positivity),
      div_le_div_iff₀ (by positivity) hN0]
    have h := abs_residueCount_sub_le q r N hq
    have hqN : (q : ℝ) * ((N : ℝ) / q) = (N : ℝ) := by field_simp
    nlinarith [abs_nonneg ((residueCount q r N : ℝ) - (N : ℝ) / q)]
  have htend : Tendsto (fun N : ℕ => (q : ℝ) / N) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (q : ℝ)
  have h := squeeze_zero_norm' hbound htend
  have h2 := h.add (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℕ)))
  simpa using h2

/-- **Main result.** For a fixed modulus `q ≥ 1` and residues `r, s`, the number of pairs
`(a, b) ∈ [0, N)^2` with `a ≡ r [MOD q]` and `b ≡ s [MOD q]` is asymptotic to the main term
`N ^ 2 / q ^ 2`. -/
