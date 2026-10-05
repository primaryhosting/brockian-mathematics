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

lemma subinterval_bounds (hg : MonotoneOn g (Icc (0:ℝ) 1)) {m : ℕ} (hm : 0 < m) {i : ℕ}
    (hi : i < m) :
    g ((i : ℝ) / m) * (1 / m) ≤ (∫ t in ((i : ℝ) / m)..(((i : ℝ) + 1) / m), g t)
      ∧ (∫ t in ((i : ℝ) / m)..(((i : ℝ) + 1) / m), g t) ≤ g (((i : ℝ) + 1) / m) * (1 / m) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hle : (i : ℝ) / m ≤ ((i : ℝ) + 1) / m := div_le_succ_div hm
  have hsub : uIcc ((i : ℝ) / m) (((i : ℝ) + 1) / m) ⊆ Icc (0:ℝ) 1 := by
    rw [Set.uIcc_of_le hle]
    exact Set.Icc_subset_Icc (div_mem_Icc hm (le_of_lt hi)).1 (succ_div_mem_Icc hm hi).2
  have hsub' : Icc ((i : ℝ) / m) (((i : ℝ) + 1) / m) ⊆ Icc (0:ℝ) 1 := by
    rw [← Set.uIcc_of_le hle]; exact hsub
  have hgint : IntervalIntegrable g volume ((i : ℝ) / m) (((i : ℝ) + 1) / m) :=
    (hg.mono hsub).intervalIntegrable
  have hwidth : ((i : ℝ) + 1) / m - (i : ℝ) / m = 1 / m := by field_simp; ring
  have hlo : ∀ t ∈ Icc ((i : ℝ) / m) (((i : ℝ) + 1) / m), g ((i : ℝ) / m) ≤ g t := fun t ht =>
    hg (div_mem_Icc hm (le_of_lt hi)) (hsub' ht) ht.1
  have hhi : ∀ t ∈ Icc ((i : ℝ) / m) (((i : ℝ) + 1) / m), g t ≤ g (((i : ℝ) + 1) / m) := fun t ht =>
    hg (hsub' ht) (succ_div_mem_Icc hm hi) ht.2
  constructor
  · have hmono := intervalIntegral.integral_mono_on (f := fun _ : ℝ => g ((i : ℝ) / m)) (g := g)
      hle intervalIntegrable_const hgint hlo
    calc g ((i : ℝ) / m) * (1 / m)
        = (((i : ℝ) + 1) / m - (i : ℝ) / m) • g ((i : ℝ) / m) := by
          rw [hwidth, smul_eq_mul, mul_comm]
      _ ≤ _ := by rw [← intervalIntegral.integral_const]; exact hmono
  · have hmono := intervalIntegral.integral_mono_on (f := g)
      (g := fun _ : ℝ => g (((i : ℝ) + 1) / m)) hle hgint intervalIntegrable_const hhi
    calc (∫ t in ((i : ℝ) / m)..(((i : ℝ) + 1) / m), g t)
        ≤ (((i : ℝ) + 1) / m - (i : ℝ) / m) • g (((i : ℝ) + 1) / m) := by
          rw [← intervalIntegral.integral_const]; exact hmono
      _ = g (((i : ℝ) + 1) / m) * (1 / m) := by rw [hwidth, smul_eq_mul, mul_comm]

/-- Lower and upper Riemann-type bounds for the weighted count. -/
