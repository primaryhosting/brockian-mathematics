import Mathlib

/-!
# Bloch Sphere Bijection
Category: Quantum Computing
Target: QC.bloch_sphere_bijection
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

namespace QC

/-- A pure qubit state: a unit vector in `ℂ²`. -/

theorem bloch_injective : Function.Injective bloch := by
  intro a b hab
  induction a using Quotient.inductionOn with
  | _ v =>
    induction b using Quotient.inductionOn with
    | _ w =>
      obtain ⟨v, hv⟩ := v
      obtain ⟨w, hw⟩ := w
      rw [bloch_mk, bloch_mk] at hab
      -- extract the three coordinate equalities
      have h0 : 2 * ((starRingEnd ℂ) (v 0) * v 1).re = 2 * ((starRingEnd ℂ) (w 0) * w 1).re := by
        have := congrArg (fun p => p.1 0) hab; simpa [blochRaw] using this
      have h1 : 2 * ((starRingEnd ℂ) (v 0) * v 1).im = 2 * ((starRingEnd ℂ) (w 0) * w 1).im := by
        have := congrArg (fun p => p.1 1) hab; simpa [blochRaw] using this
      have h2 : ‖v 0‖ ^ 2 - ‖v 1‖ ^ 2 = ‖w 0‖ ^ 2 - ‖w 1‖ ^ 2 := by
        have := congrArg (fun p => p.1 2) hab; simpa [blochRaw] using this
      have hprod : (starRingEnd ℂ) (v 0) * v 1 = (starRingEnd ℂ) (w 0) * w 1 :=
        Complex.ext (by linarith) (by linarith)
      have hn0 : ‖v 0‖ ^ 2 = ‖w 0‖ ^ 2 := by linarith
      have hn1 : ‖v 1‖ ^ 2 = ‖w 1‖ ^ 2 := by linarith
      apply Quotient.sound
      by_cases hv0 : v 0 = 0
      · -- then v 1 has norm 1, and w 0 = 0 as well
        have hw0 : w 0 = 0 := by
          have : ‖w 0‖ ^ 2 = 0 := by rw [← hn0, hv0]; simp
          have : ‖w 0‖ = 0 := by nlinarith [norm_nonneg (w 0)]
          simpa using this
        have hv1 : ‖v 1‖ = 1 := by
          rw [hv0] at hv; simp at hv
          rcases hv with h | h
          · exact h
          · nlinarith [norm_nonneg (v 1)]
        have hw1 : ‖w 1‖ = 1 := by
          rw [hw0] at hw; simp at hw
          rcases hw with h | h
          · exact h
          · nlinarith [norm_nonneg (w 1)]
        have hv1ne : v 1 ≠ 0 := by
          intro h; rw [h] at hv1; simp at hv1
        refine ⟨w 1 / v 1, ?_, ?_⟩
        · rw [norm_div, hv1, hw1]; norm_num
        · intro i
          fin_cases i
          · simp [hv0, hw0]
          · show w 1 = w 1 / v 1 * v 1
            field_simp
      · -- v 0 ≠ 0, so w 0 ≠ 0
        have hw0 : w 0 ≠ 0 := by
          intro h
          apply hv0
          have : ‖v 0‖ ^ 2 = 0 := by rw [hn0, h]; simp
          have : ‖v 0‖ = 0 := by nlinarith [norm_nonneg (v 0)]
          simpa using this
        refine ⟨w 0 / v 0, ?_, ?_⟩
        · rw [norm_div]
          have : ‖v 0‖ = ‖w 0‖ := by
            nlinarith [norm_nonneg (v 0), norm_nonneg (w 0)]
          rw [this, div_self]
          simpa using hw0
        · intro i
          fin_cases i
          · show w 0 = w 0 / v 0 * v 0
            field_simp
          · show w 1 = w 0 / v 0 * v 1
            rw [div_mul_eq_mul_div, eq_div_iff hv0]
            -- w 1 * v 0 = w 0 * v 1
            have key : (starRingEnd ℂ) (v 0) * (w 1 * v 0) =
                (starRingEnd ℂ) (v 0) * (w 0 * v 1) := by
              have e1 : (starRingEnd ℂ) (v 0) * v 1 = (starRingEnd ℂ) (w 0) * w 1 := hprod
              have hvv : (starRingEnd ℂ) (v 0) * v 0 = (Complex.normSq (v 0) : ℂ) := by
                rw [mul_comm]; exact Complex.mul_conj (v 0)
              have hww : (starRingEnd ℂ) (w 0) * w 0 = (Complex.normSq (w 0) : ℂ) := by
                rw [mul_comm]; exact Complex.mul_conj (w 0)
              have hnn : Complex.normSq (v 0) = Complex.normSq (w 0) := by
                rw [← Complex.sq_norm, ← Complex.sq_norm]; exact hn0
              calc (starRingEnd ℂ) (v 0) * (w 1 * v 0)
                  = ((starRingEnd ℂ) (v 0) * v 0) * w 1 := by ring
                _ = (Complex.normSq (v 0) : ℂ) * w 1 := by rw [hvv]
                _ = (Complex.normSq (w 0) : ℂ) * w 1 := by rw [hnn]
                _ = ((starRingEnd ℂ) (w 0) * w 0) * w 1 := by rw [hww]
                _ = ((starRingEnd ℂ) (w 0) * w 1) * w 0 := by ring
                _ = ((starRingEnd ℂ) (v 0) * v 1) * w 0 := by rw [e1]
                _ = (starRingEnd ℂ) (v 0) * (w 0 * v 1) := by ring
            have hconj : (starRingEnd ℂ) (v 0) ≠ 0 := by
              simpa using hv0
            exact mul_left_cancel₀ hconj key

