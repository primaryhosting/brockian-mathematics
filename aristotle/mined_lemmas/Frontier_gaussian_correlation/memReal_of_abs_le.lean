import Mathlib

/-!
# Gaussian Correlation
Category: Frontier — Fields Medal Work
Target: Frontier.gaussian_correlation
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

namespace Frontier

open MeasureTheory

/-! ## The standard Gaussian measure and the statement of the inequality -/

/-- The standard Gaussian (probability) measure on `ℝ ^ n`, realised as the `n`-fold product
of the one-dimensional standard Gaussian `N(0,1)`. -/

theorem memReal_of_abs_le {S : Set ℝ} (hc : Convex ℝ S) (hs : ∀ x ∈ S, -x ∈ S)
    {a b : ℝ} (ha : a ∈ S) (hab : |b| ≤ |a|) : b ∈ S := by
  by_cases ha0 : a = 0
  · have hb : b = 0 := by
      rw [ha0] at hab
      simpa using abs_nonpos_iff.mp (by simpa using hab)
    rw [hb, ← ha0]
    exact ha
  · set t : ℝ := b / a with ht
    have hta : t * a = b := div_mul_cancel₀ _ ha0
    have htabs : |t| ≤ 1 := by
      rw [ht, abs_div, div_le_one (abs_pos.mpr ha0)]
      exact hab
    have ht1 : -1 ≤ t := neg_le_of_abs_le htabs
    have ht2 : t ≤ 1 := le_of_abs_le htabs
    have hmem : ((1 + t) / 2) • a + ((1 - t) / 2) • (-a) ∈ S :=
      hc ha (hs a ha) (by linarith) (by linarith) (by ring)
    have hval : ((1 + t) / 2) • a + ((1 - t) / 2) • (-a) = b := by
      simp only [smul_eq_mul]
      rw [← hta]
      ring
    rwa [hval] at hmem

/-- Any two symmetric convex subsets of the real line are nested. -/
