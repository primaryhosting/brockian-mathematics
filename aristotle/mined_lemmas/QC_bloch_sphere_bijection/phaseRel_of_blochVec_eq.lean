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
# Bloch Sphere Bijection
Category: Quantum Computing
Target: QC.bloch_sphere_bijection
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to precede any module docstring, so the header above is
-- repeated as the module docstring below.)
import Mathlib

/-!
# Bloch Sphere Bijection
Category: Quantum Computing
Target: QC.bloch_sphere_bijection
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Complex

/-- A (normalised) pure qubit state vector: a unit vector `(a, b)` in `ℂ²`,
representing `a|0⟩ + b|1⟩`. -/

lemma phaseRel_of_blochVec_eq {v w : Qubit}
    (h : blochVec (v : ℂ × ℂ) = blochVec (w : ℂ × ℂ)) : phaseRel v w := by
  obtain ⟨⟨a, b⟩, hv⟩ := v
  obtain ⟨⟨c, d⟩, hw⟩ := w
  simp only [blochVec] at h
  have e0 := congrFun (congrArg WithLp.ofLp h) 0
  have e1 := congrFun (congrArg WithLp.ofLp h) 1
  have e2 := congrFun (congrArg WithLp.ofLp h) 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons] at e0 e1 e2
  have habs : (starRingEnd ℂ) a * b = (starRingEnd ℂ) c * d :=
    Complex.ext (by linarith) (by linarith)
  have hn1 : normSq a = normSq c := by linarith
  have hn2 : normSq b = normSq d := by linarith
  by_cases ha : a = 0
  · have hc : c = 0 := by
      rw [← normSq_eq_zero, ← hn1, ha]; simp
    have hb : b ≠ 0 := by
      intro hb0
      rw [ha, hb0] at hv; simp at hv
    refine ⟨d / b, ?_, ?_, ?_⟩
    · have : ‖d‖ = ‖b‖ := by
        show Real.sqrt (normSq d) = Real.sqrt (normSq b)
        rw [hn2]
      rw [norm_div, this, div_self (by simpa using hb)]
    · show c = d / b * a
      rw [hc, ha, mul_zero]
    · show d = d / b * b
      field_simp
  · have hca : (starRingEnd ℂ) a ≠ 0 := by simpa using ha
    have hcb : c * b = a * d := by
      have hcc : c * (starRingEnd ℂ) c = (normSq c : ℂ) := mul_conj c
      have haa : a * (starRingEnd ℂ) a = (normSq a : ℂ) := mul_conj a
      have h1 : (starRingEnd ℂ) a * (c * b) = (starRingEnd ℂ) a * (a * d) := by
        calc (starRingEnd ℂ) a * (c * b) = c * ((starRingEnd ℂ) a * b) := by ring
          _ = c * ((starRingEnd ℂ) c * d) := by rw [habs]
          _ = (c * (starRingEnd ℂ) c) * d := by ring
          _ = (normSq c : ℂ) * d := by rw [hcc]
          _ = (normSq a : ℂ) * d := by rw [hn1]
          _ = (a * (starRingEnd ℂ) a) * d := by rw [haa]
          _ = (starRingEnd ℂ) a * (a * d) := by ring
      exact mul_left_cancel₀ hca h1
    refine ⟨c / a, ?_, ?_, ?_⟩
    · have hac : ‖c‖ = ‖a‖ := by
        show Real.sqrt (normSq c) = Real.sqrt (normSq a)
        rw [hn1]
      rw [norm_div, hac, div_self (by simpa using ha)]
    · show c = c / a * a
      field_simp
    · show d = c / a * b
      field_simp
      linear_combination -hcb

