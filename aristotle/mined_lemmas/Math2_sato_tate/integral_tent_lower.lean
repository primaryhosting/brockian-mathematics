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

lemma integral_tent_lower {a b delta : ℝ} (hd : 0 < delta) (h0 : 0 ≤ a)
    (hb : b ≤ Real.pi) :
    satoTateCDF (b - delta) - satoTateCDF (a + delta)
      ≤ ∫ x in (0:ℝ)..Real.pi, tent a b delta x * satoTateDensity x := by
  have hpi := Real.pi_pos
  set g : ℝ → ℝ := fun x => tent a b delta x * satoTateDensity x with hg
  have hgc : Continuous g := (continuous_tent a b delta).mul continuous_satoTateDensity
  have hint : ∀ u v : ℝ, IntervalIntegrable g MeasureTheory.volume u v :=
    fun u v => hgc.intervalIntegrable u v
  have hgnn : ∀ x, 0 ≤ g x := fun x =>
    mul_nonneg (tent_nonneg _ _ _ _) (satoTateDensity_nonneg x)
  rcases le_or_gt (a + delta) (b - delta) with hle | hlt
  · have h0u : (0:ℝ) ≤ a + delta := by linarith
    have hvpi : b - delta ≤ Real.pi := by linarith
    have hsplit : (∫ x in (0:ℝ)..Real.pi, g x)
        = (∫ x in (0:ℝ)..(a + delta), g x) + (∫ x in (a + delta)..(b - delta), g x)
          + (∫ x in (b - delta)..Real.pi, g x) := by
      rw [intervalIntegral.integral_add_adjacent_intervals (hint 0 _) (hint _ _),
        intervalIntegral.integral_add_adjacent_intervals (hint 0 _) (hint _ Real.pi)]
    have h1 : 0 ≤ ∫ x in (0:ℝ)..(a + delta), g x :=
      intervalIntegral.integral_nonneg h0u (fun t _ => hgnn t)
    have h3 : 0 ≤ ∫ x in (b - delta)..Real.pi, g x :=
      intervalIntegral.integral_nonneg hvpi (fun t _ => hgnn t)
    have h2 : (∫ x in (a + delta)..(b - delta), g x)
        = satoTateCDF (b - delta) - satoTateCDF (a + delta) := by
      rw [← integral_satoTateDensity]
      refine intervalIntegral.integral_congr ?_
      intro x hx
      have hx' : a + delta ≤ x ∧ x ≤ b - delta := by
        rw [Set.uIcc_of_le hle] at hx; exact ⟨hx.1, hx.2⟩
      simp [hg, tent_eq_one hd hx'.1 hx'.2]
    rw [hsplit, h2]
    linarith
  · have : satoTateCDF (b - delta) ≤ satoTateCDF (a + delta) := satoTateCDF_mono hlt.le
    have h4 : 0 ≤ ∫ x in (0:ℝ)..Real.pi, g x :=
      intervalIntegral.integral_nonneg hpi.le (fun t _ => hgnn t)
    linarith

/-! ## Counting comparison -/

