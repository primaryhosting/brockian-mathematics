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

set_option grind.warning false

namespace QC

open Complex

/-- A pure state of a single qubit: a unit vector in `ℂ²`. -/
abbrev PureQubit : Type := Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1

/-- The 2-sphere `S²`, the unit sphere of `ℝ³`. -/
abbrev S2 : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1


lemma blochMap_injective : Function.Injective blochMap := by
  intro q1 q2 h
  induction q1 using Quotient.inductionOn with
  | _ v =>
  induction q2 using Quotient.inductionOn with
  | _ w =>
  have hv : Complex.normSq ((v : EuclideanSpace ℂ (Fin 2)) 0)
      + Complex.normSq ((v : EuclideanSpace ℂ (Fin 2)) 1) = 1 :=
    (mem_sphere_two_iff _).1 v.2
  have hw : Complex.normSq ((w : EuclideanSpace ℂ (Fin 2)) 0)
      + Complex.normSq ((w : EuclideanSpace ℂ (Fin 2)) 1) = 1 :=
    (mem_sphere_two_iff _).1 w.2
  have hvec : blochVec (v : EuclideanSpace ℂ (Fin 2))
      = blochVec (w : EuclideanSpace ℂ (Fin 2)) := congrArg Subtype.val h
  set a1 := (v : EuclideanSpace ℂ (Fin 2)) 0 with ha1
  set b1 := (v : EuclideanSpace ℂ (Fin 2)) 1 with hb1
  set a2 := (w : EuclideanSpace ℂ (Fin 2)) 0 with ha2
  set b2 := (w : EuclideanSpace ℂ (Fin 2)) 1 with hb2
  have h0 : 2 * ((starRingEnd ℂ) a1 * b1).re = 2 * ((starRingEnd ℂ) a2 * b2).re :=
    congrArg (fun p : EuclideanSpace ℝ (Fin 3) => p 0) hvec
  have h1 : 2 * ((starRingEnd ℂ) a1 * b1).im = 2 * ((starRingEnd ℂ) a2 * b2).im :=
    congrArg (fun p : EuclideanSpace ℝ (Fin 3) => p 1) hvec
  have h2 : Complex.normSq a1 - Complex.normSq b1 = Complex.normSq a2 - Complex.normSq b2 :=
    congrArg (fun p : EuclideanSpace ℝ (Fin 3) => p 2) hvec
  have hconj : (starRingEnd ℂ) a1 * b1 = (starRingEnd ℂ) a2 * b2 := by
    apply Complex.ext <;> linarith
  have hna : Complex.normSq a1 = Complex.normSq a2 := by linarith
  have hnb : Complex.normSq b1 = Complex.normSq b2 := by linarith
  apply Quotient.sound
  by_cases ha : a1 = 0
  · have ha2' : a2 = 0 := by
      have : Complex.normSq a2 = 0 := by rw [← hna, ha]; simp
      exact (Complex.normSq_eq_zero.1 this)
    have hb1n : Complex.normSq b1 = 1 := by rw [ha] at hv; simpa using hv
    have hb1ne : b1 ≠ 0 := by
      intro hcon; rw [hcon] at hb1n; simp at hb1n
    refine ⟨b2 / b1, ?_, ?_⟩
    · rw [norm_div, norm_eq_one_of_normSq_eq_one hb1n,
        norm_eq_one_of_normSq_eq_one (hnb ▸ hb1n)]
      norm_num
    · refine PiLp.ext (fun i => ?_)
      fin_cases i
      · show a2 = (b2 / b1) * a1
        rw [ha, ha2', mul_zero]
      · show b2 = (b2 / b1) * b1
        field_simp
  · have ha2' : a2 ≠ 0 := by
      intro hcon
      apply ha
      have : Complex.normSq a1 = 0 := by rw [hna, hcon]; simp
      exact Complex.normSq_eq_zero.1 this
    have hc2 : (starRingEnd ℂ) a2 ≠ 0 := by
      simpa using ha2'
    have hna1 : (a1 : ℂ) * (starRingEnd ℂ) a1 = (Complex.normSq a1 : ℂ) := by
      rw [mul_comm, ← Complex.normSq_eq_conj_mul_self]
    have hna2 : (a2 : ℂ) * (starRingEnd ℂ) a2 = (Complex.normSq a2 : ℂ) := by
      rw [mul_comm, ← Complex.normSq_eq_conj_mul_self]
    refine ⟨a2 / a1, ?_, ?_⟩
    · have hn1 : ‖a1‖ = ‖a2‖ := by
        have e1 : ‖a1‖ ^ 2 = ‖a2‖ ^ 2 := by
          rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, hna]
        nlinarith [norm_nonneg a1, norm_nonneg a2]
      rw [norm_div, hn1, div_self]
      simpa using ha2'
    · refine PiLp.ext (fun i => ?_)
      fin_cases i
      · show a2 = (a2 / a1) * a1
        field_simp
      · show b2 = (a2 / a1) * b1
        rw [div_mul_eq_mul_div, eq_div_iff ha]
        apply mul_right_cancel₀ hc2
        calc b2 * a1 * (starRingEnd ℂ) a2
            = a1 * ((starRingEnd ℂ) a2 * b2) := by ring
          _ = a1 * ((starRingEnd ℂ) a1 * b1) := by rw [hconj]
          _ = (a1 * (starRingEnd ℂ) a1) * b1 := by ring
          _ = (Complex.normSq a1 : ℂ) * b1 := by rw [hna1]
          _ = (Complex.normSq a2 : ℂ) * b1 := by rw [hna]
          _ = (a2 * (starRingEnd ℂ) a2) * b1 := by rw [hna2]
          _ = a2 * b1 * (starRingEnd ℂ) a2 := by ring


