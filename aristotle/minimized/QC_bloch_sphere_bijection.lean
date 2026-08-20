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

/-- A pure qubit state: a unit vector `(a, b)` in `ℂ²`. -/
structure Qubit where
  a : ℂ
  b : ℂ
  norm_eq : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1

/-- A point of the 2-sphere `S² ⊆ ℝ³`. -/
@[ext]
structure Sphere2 where
  x : ℝ
  y : ℝ
  z : ℝ
  norm_eq : x ^ 2 + y ^ 2 + z ^ 2 = 1

lemma sq_norm_complex (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

lemma Qubit.components (v : Qubit) :
    v.a.re ^ 2 + v.a.im ^ 2 + (v.b.re ^ 2 + v.b.im ^ 2) = 1 := by
  have := v.norm_eq
  rw [sq_norm_complex, sq_norm_complex] at this
  linarith

/-- Two qubit states are equivalent when they differ by a global phase. -/

def PhaseEq (v w : Qubit) : Prop :=
  ∃ c : ℂ, ‖c‖ = 1 ∧ w.a = c * v.a ∧ w.b = c * v.b

def PureState : Type := Quotient phaseSetoid

/-- The Bloch vector of a qubit state. -/

def blochRaw (v : Qubit) : Sphere2 :=
  ⟨2 * (v.a.re * v.b.re + v.a.im * v.b.im),
   2 * (v.a.re * v.b.im - v.a.im * v.b.re),
   (v.a.re ^ 2 + v.a.im ^ 2) - (v.b.re ^ 2 + v.b.im ^ 2), by
    have h := v.components
    nlinarith [h, sq_nonneg (v.a.re * v.b.re + v.a.im * v.b.im)]⟩

lemma blochRaw_respects {v w : Qubit} (h : PhaseEq v w) : blochRaw v = blochRaw w := by
  obtain ⟨c, hc, ha, hb⟩ := h
  have hc' : c.re ^ 2 + c.im ^ 2 = 1 := by
    have : ‖c‖ ^ 2 = 1 := by rw [hc]; norm_num
    rw [sq_norm_complex] at this; exact this
  have hare : w.a.re = c.re * v.a.re - c.im * v.a.im := by rw [ha]; simp
  have haim : w.a.im = c.re * v.a.im + c.im * v.a.re := by rw [ha]; simp
  have hbre : w.b.re = c.re * v.b.re - c.im * v.b.im := by rw [hb]; simp
  have hbim : w.b.im = c.re * v.b.im + c.im * v.b.re := by rw [hb]; simp
  ext
  · dsimp [blochRaw]
    rw [hare, haim, hbre, hbim]
    linear_combination (-2 * (v.a.re * v.b.re + v.a.im * v.b.im)) * hc'
  · dsimp [blochRaw]
    rw [hare, haim, hbre, hbim]
    linear_combination (-2 * (v.a.re * v.b.im - v.a.im * v.b.re)) * hc'
  · dsimp [blochRaw]
    rw [hare, haim, hbre, hbim]
    linear_combination (-((v.a.re ^ 2 + v.a.im ^ 2) - (v.b.re ^ 2 + v.b.im ^ 2))) * hc'

/-- The Bloch map on states modulo global phase. -/

def bloch : PureState → Sphere2 :=
  Quotient.lift blochRaw (fun _ _ h => blochRaw_respects h)

lemma bloch_mk (v : Qubit) : bloch (Quotient.mk phaseSetoid v) = blochRaw v := rfl

lemma norm_a_eq {v w : Qubit} (h : blochRaw v = blochRaw w) : ‖v.a‖ = ‖w.a‖ := by
  have hz : (v.a.re ^ 2 + v.a.im ^ 2) - (v.b.re ^ 2 + v.b.im ^ 2)
      = (w.a.re ^ 2 + w.a.im ^ 2) - (w.b.re ^ 2 + w.b.im ^ 2) := congrArg Sphere2.z h
  have hv := v.components
  have hw := w.components
  have : ‖v.a‖ ^ 2 = ‖w.a‖ ^ 2 := by
    rw [sq_norm_complex, sq_norm_complex]; linarith
  have h1 : (0:ℝ) ≤ ‖v.a‖ := norm_nonneg _
  have h2 : (0:ℝ) ≤ ‖w.a‖ := norm_nonneg _
  nlinarith

lemma norm_b_eq {v w : Qubit} (h : blochRaw v = blochRaw w) : ‖v.b‖ = ‖w.b‖ := by
  have hz : (v.a.re ^ 2 + v.a.im ^ 2) - (v.b.re ^ 2 + v.b.im ^ 2)
      = (w.a.re ^ 2 + w.a.im ^ 2) - (w.b.re ^ 2 + w.b.im ^ 2) := congrArg Sphere2.z h
  have hv := v.components
  have hw := w.components
  have : ‖v.b‖ ^ 2 = ‖w.b‖ ^ 2 := by
    rw [sq_norm_complex, sq_norm_complex]; linarith
  have h1 : (0:ℝ) ≤ ‖v.b‖ := norm_nonneg _
  have h2 : (0:ℝ) ≤ ‖w.b‖ := norm_nonneg _
  nlinarith

lemma conj_mul_eq {v w : Qubit} (h : blochRaw v = blochRaw w) :
    (starRingEnd ℂ) v.a * v.b = (starRingEnd ℂ) w.a * w.b := by
  have hx : 2 * (v.a.re * v.b.re + v.a.im * v.b.im)
      = 2 * (w.a.re * w.b.re + w.a.im * w.b.im) := congrArg Sphere2.x h
  have hy : 2 * (v.a.re * v.b.im - v.a.im * v.b.re)
      = 2 * (w.a.re * w.b.im - w.a.im * w.b.re) := congrArg Sphere2.y h
  apply Complex.ext <;> simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re,
    Complex.conj_im] <;> linarith

lemma blochRaw_inj {v w : Qubit} (h : blochRaw v = blochRaw w) : PhaseEq v w := by
  have hna := norm_a_eq h
  have hnb := norm_b_eq h
  have hp := conj_mul_eq h
  by_cases hva : v.a = 0
  · have hwa : w.a = 0 := by
      have : ‖w.a‖ = 0 := by rw [← hna, hva]; simp
      simpa using this
    have hvb : v.b ≠ 0 := by
      intro h0
      have := v.norm_eq
      rw [hva, h0] at this
      simp at this
    have hwb : w.b ≠ 0 := by
      intro h0
      apply hvb
      have : ‖v.b‖ = 0 := by rw [hnb, h0]; simp
      simpa using this
    refine ⟨w.b / v.b, ?_, ?_, ?_⟩
    · rw [norm_div, hnb]
      exact div_self (by simpa using hwb)
    · rw [hva, hwa]; ring
    · field_simp
  · have hwa : w.a ≠ 0 := by
      intro h0
      apply hva
      have : ‖v.a‖ = 0 := by rw [hna, h0]; simp
      simpa using this
    have hns : Complex.normSq v.a = Complex.normSq w.a := by
      rw [← Complex.sq_norm, ← Complex.sq_norm, hna]
    have hcc : (starRingEnd ℂ) w.a ≠ 0 := by simpa using hwa
    have key : w.b * v.a = w.a * v.b := by
      apply mul_right_cancel₀ hcc
      calc w.b * v.a * (starRingEnd ℂ) w.a
          = ((starRingEnd ℂ) w.a * w.b) * v.a := by ring
        _ = ((starRingEnd ℂ) v.a * v.b) * v.a := by rw [hp]
        _ = (v.a * (starRingEnd ℂ) v.a) * v.b := by ring
        _ = ((Complex.normSq v.a : ℝ) : ℂ) * v.b := by rw [Complex.mul_conj]
        _ = ((Complex.normSq w.a : ℝ) : ℂ) * v.b := by rw [hns]
        _ = (w.a * (starRingEnd ℂ) w.a) * v.b := by rw [Complex.mul_conj]
        _ = w.a * v.b * (starRingEnd ℂ) w.a := by ring
    refine ⟨w.a / v.a, ?_, ?_, ?_⟩
    · rw [norm_div, hna]
      exact div_self (by simpa using hwa)
    · field_simp
    · field_simp
      linear_combination key

lemma bloch_injective : Function.Injective bloch := by
  intro p q h
  induction p using Quotient.inductionOn with
  | _ v =>
    induction q using Quotient.inductionOn with
    | _ w =>
      exact Quotient.sound (blochRaw_inj h)

lemma bloch_surjective : Function.Surjective bloch := by
  intro s
  obtain ⟨x, y, z, hs⟩ := s
  by_cases hz : z = -1
  · have hx : x = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
    have hy : y = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
    refine ⟨Quotient.mk phaseSetoid ⟨0, 1, by simp⟩, ?_⟩
    rw [bloch_mk]
    apply Sphere2.ext <;> simp [blochRaw, hx, hy, hz]
  · have hz1 : -1 < z := by
      rcases lt_trichotomy z (-1) with h1 | h1 | h1
      · nlinarith [sq_nonneg x, sq_nonneg y]
      · exact absurd h1 hz
      · exact h1
    set r : ℝ := Real.sqrt ((1 + z) / 2) with hrdef
    have hr2 : r ^ 2 = (1 + z) / 2 := Real.sq_sqrt (by linarith)
    have hr0 : 0 < r := Real.sqrt_pos.mpr (by linarith)
    have hrne : r ≠ 0 := ne_of_gt hr0
    refine ⟨Quotient.mk phaseSetoid ⟨(r : ℂ), (↑(x / (2 * r)) + ↑(y / (2 * r)) * Complex.I), ?_⟩, ?_⟩
    · rw [sq_norm_complex, sq_norm_complex]
      simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im,
        Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
      field_simp
      nlinarith [hr2, hs]
    · rw [bloch_mk]
      apply Sphere2.ext <;>
        simp only [blochRaw, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
          Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] <;>
        field_simp <;> nlinarith [hr2, hs]

/-- **Bloch sphere bijection**: pure qubit states modulo global phase are in bijection
with the points of the 2-sphere `S²`. -/

theorem bloch_sphere_bijection : Function.Bijective bloch :=
  ⟨bloch_injective, bloch_surjective⟩

end QC
