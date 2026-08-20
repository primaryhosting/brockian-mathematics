/-
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
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

open Filter Topology

/-! ## The Sato–Tate measure -/

/-- The density of the Sato–Tate measure `(2/π) sin²θ dθ` on `[0, π]`. -/

lemma integral_tent_upper {a b delta : ℝ} (hd : 0 < delta) (h0 : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ Real.pi) :
    (∫ x in (0:ℝ)..Real.pi, tent (a - delta) (b + delta) delta x * satoTateDensity x)
      ≤ satoTateCDF (b + delta) - satoTateCDF (a - delta) := by
  have hpi := Real.pi_pos
  set c : ℝ := a - delta with hc
  set d : ℝ := b + delta with hdd
  set g : ℝ → ℝ := fun x => tent c d delta x * satoTateDensity x with hg
  have hgc : Continuous g := (continuous_tent c d delta).mul continuous_satoTateDensity
  have hint : ∀ u v : ℝ, IntervalIntegrable g MeasureTheory.volume u v :=
    fun u v => hgc.intervalIntegrable u v
  set a1 : ℝ := max 0 c with ha1
  set b1 : ℝ := min Real.pi d with hb1
  have h0a1 : (0:ℝ) ≤ a1 := le_max_left _ _
  have ha1b1 : a1 ≤ b1 :=
    max_le (le_min hpi.le (by simp [hdd]; linarith)) (le_min (by simp [hc]; linarith)
      (by simp [hc, hdd]; linarith))
  have hb1pi : b1 ≤ Real.pi := min_le_left _ _
  have hsplit : (∫ x in (0:ℝ)..Real.pi, g x)
      = (∫ x in (0:ℝ)..a1, g x) + (∫ x in a1..b1, g x) + (∫ x in b1..Real.pi, g x) := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hint 0 a1) (hint a1 b1),
      intervalIntegral.integral_add_adjacent_intervals (hint 0 b1) (hint b1 Real.pi)]
  have hleft : (∫ x in (0:ℝ)..a1, g x) = 0 := by
    rcases le_or_gt c 0 with hcle | hcpos
    · have : a1 = 0 := by simp [ha1, max_eq_left hcle]
      rw [this, intervalIntegral.integral_same]
    · have ha1c : a1 = c := max_eq_right hcpos.le
      rw [show (fun x => g x) = g from rfl]
      rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) ?_, intervalIntegral.integral_zero]
      intro x hx
      rw [ha1c] at hx
      rw [Set.uIcc_of_le hcpos.le] at hx
      simp [tent_eq_zero_left hd hx.2]
  have hright : (∫ x in b1..Real.pi, g x) = 0 := by
    rcases le_or_gt Real.pi d with hdge | hdlt
    · have : b1 = Real.pi := min_eq_left hdge
      rw [this, intervalIntegral.integral_same]
    · have hb1d : b1 = d := min_eq_right hdlt.le
      rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) ?_, intervalIntegral.integral_zero]
      intro x hx
      rw [hb1d] at hx
      rw [Set.uIcc_of_le hdlt.le] at hx
      simp [hg, tent_eq_zero_right hd hx.1]
  have hmid : (∫ x in a1..b1, g x) ≤ satoTateCDF b1 - satoTateCDF a1 := by
    rw [← integral_satoTateDensity]
    refine intervalIntegral.integral_mono_on ha1b1 (hint a1 b1)
      (continuous_satoTateDensity.intervalIntegrable _ _) ?_
    intro x _
    have h1 : tent c d delta x ≤ 1 := tent_le_one _ _ _ _
    have h2 : 0 ≤ satoTateDensity x := satoTateDensity_nonneg x
    calc tent c d delta x * satoTateDensity x ≤ 1 * satoTateDensity x := by nlinarith
      _ = satoTateDensity x := one_mul _
  have hmono1 : satoTateCDF b1 ≤ satoTateCDF d := satoTateCDF_mono (min_le_right _ _)
  have hmono2 : satoTateCDF c ≤ satoTateCDF a1 := satoTateCDF_mono (le_max_right _ _)
  rw [hsplit, hleft, hright]
  linarith

