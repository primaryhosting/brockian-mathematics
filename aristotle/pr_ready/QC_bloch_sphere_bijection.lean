/-!
# Bloch Sphere Bijection
Category: Quantum Computing
Target: QC.bloch_sphere_bijection
Statement: Pure qubit states modulo global phase biject with points of the 2-sphere S².
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-!
# Bloch Sphere Bijection
Category: Quantum Computing
Target: QC.bloch_sphere_bijection
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex

namespace QC

/-- A pure state of a qubit: a unit vector `(a, b)` in `ℂ²`. -/
structure Qubit where
  a : ℂ
  b : ℂ
  unit : normSq a + normSq b = 1

/-- Two pure qubit states are equivalent when they differ by a global phase. -/
def PhaseEq (v w : Qubit) : Prop :=
  ∃ z : ℂ, ‖z‖ = 1 ∧ w.a = z * v.a ∧ w.b = z * v.b

lemma phaseEq_refl (v : Qubit) : PhaseEq v v := ⟨1, by simp, by simp, by simp⟩

lemma phaseEq_symm {v w : Qubit} (h : PhaseEq v w) : PhaseEq w v := by
  obtain ⟨z, hz, ha, hb⟩ := h
  have hz0 : z ≠ 0 := by
    intro h0; rw [h0] at hz; simp at hz
  refine ⟨z⁻¹, by simp [hz], ?_, ?_⟩
  · rw [ha, ← mul_assoc, inv_mul_cancel₀ hz0, one_mul]
  · rw [hb, ← mul_assoc, inv_mul_cancel₀ hz0, one_mul]

lemma phaseEq_trans {u v w : Qubit} (h₁ : PhaseEq u v) (h₂ : PhaseEq v w) : PhaseEq u w := by
  obtain ⟨z, hz, ha, hb⟩ := h₁
  obtain ⟨y, hy, ha', hb'⟩ := h₂
  exact ⟨y * z, by simp [hy, hz], by rw [ha', ha, mul_assoc], by rw [hb', hb, mul_assoc]⟩

instance qubitSetoid : Setoid Qubit where
  r := PhaseEq
  iseqv := ⟨phaseEq_refl, phaseEq_symm, phaseEq_trans⟩

/-- Pure qubit states modulo global phase. -/
def PureState : Type := Quotient qubitSetoid

/-- The Bloch vector of a pure qubit state:
`(2 Re(a b̄), 2 Im(a b̄), |a|² - |b|²)`. -/
def blochVec (v : Qubit) : EuclideanSpace ℝ (Fin 3) :=
  !₂[2 * (v.a * (starRingEnd ℂ) v.b).re, 2 * (v.a * (starRingEnd ℂ) v.b).im,
      normSq v.a - normSq v.b]

lemma blochVec_norm (v : Qubit) : ‖blochVec v‖ = 1 := by
  obtain ⟨a, b, h⟩ := v
  rw [blochVec, EuclideanSpace.norm_eq, Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Real.norm_eq_abs, sq_abs]
  rw [show (1:ℝ) = Real.sqrt 1 by simp]
  congr 1
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.conj_re,
    Complex.conj_im] at *
  nlinarith [h, sq_nonneg (a.re * b.re), sq_nonneg (a.im * b.im)]

lemma blochVec_phaseEq {v w : Qubit} (h : PhaseEq v w) : blochVec v = blochVec w := by
  obtain ⟨z, hz, ha, hb⟩ := h
  have hnz : normSq z = 1 := by rw [Complex.normSq_eq_norm_sq, hz]; norm_num
  have hprod : w.a * (starRingEnd ℂ) w.b = v.a * (starRingEnd ℂ) v.b := by
    rw [ha, hb, map_mul]
    calc z * v.a * ((starRingEnd ℂ) z * (starRingEnd ℂ) v.b)
        = (z * (starRingEnd ℂ) z) * (v.a * (starRingEnd ℂ) v.b) := by ring
      _ = v.a * (starRingEnd ℂ) v.b := by rw [Complex.mul_conj, hnz]; simp
  have hna : normSq w.a = normSq v.a := by rw [ha, map_mul, hnz, one_mul]
  have hnb : normSq w.b = normSq v.b := by rw [hb, map_mul, hnz, one_mul]
  rw [blochVec, blochVec, hprod, hna, hnb]

/-- The Bloch map, from pure qubit states modulo global phase to the unit sphere `S² ⊆ ℝ³`. -/
def bloch : PureState → Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  Quotient.lift (fun v => (⟨blochVec v, by simpa using blochVec_norm v⟩ :
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1))
    (fun _ _ h => Subtype.ext (blochVec_phaseEq h))

/-- Two unit vectors of `ℂ²` with the same Bloch vector differ by a global phase. -/
lemma phase_of_bloch_eq {a b c d : ℂ} (h1 : normSq a + normSq b = 1)
    (h2 : normSq c + normSq d = 1) (hprod : a * (starRingEnd ℂ) b = c * (starRingEnd ℂ) d)
    (hz : normSq a - normSq b = normSq c - normSq d) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ c = z * a ∧ d = z * b := by
  have hac : normSq a = normSq c := by linarith
  have hbd : normSq b = normSq d := by linarith
  have hnorm_ac : ‖a‖ = ‖c‖ := by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hac
    nlinarith [norm_nonneg a, norm_nonneg c]
  have hnorm_bd : ‖b‖ = ‖d‖ := by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hbd
    nlinarith [norm_nonneg b, norm_nonneg d]
  by_cases ha : a = 0
  · have hc : c = 0 := by
      have : ‖c‖ = 0 := by rw [← hnorm_ac, ha]; simp
      simpa using this
    have hb : b ≠ 0 := by
      intro hb0
      rw [ha, hb0] at h1; simp at h1
    refine ⟨d / b, ?_, by simp [ha, hc], by field_simp⟩
    rw [norm_div, ← hnorm_bd, div_self (by simpa using hb)]
  · refine ⟨c / a, ?_, by field_simp, ?_⟩
    · rw [norm_div, ← hnorm_ac, div_self (by simpa using ha)]
    · have hnz : normSq (c / a) = 1 := by
        rw [Complex.normSq_eq_norm_sq, norm_div, ← hnorm_ac,
          div_self (by simpa using ha)]; norm_num
      have key : (starRingEnd ℂ) b = (c / a) * (starRingEnd ℂ) d := by
        field_simp
        rw [mul_comm] at hprod ⊢
        linear_combination hprod
      have hb' : b = (starRingEnd ℂ) (c / a) * d := by
        have := congrArg (starRingEnd ℂ) key
        simpa [map_mul] using this
      rw [hb', ← mul_assoc, Complex.mul_conj, hnz]
      simp

lemma bloch_injective : Function.Injective bloch := by
  intro q₁ q₂ h
  induction q₁ using Quotient.inductionOn with
  | h v =>
    induction q₂ using Quotient.inductionOn with
    | h w =>
      have hv : blochVec v = blochVec w := congrArg Subtype.val h
      obtain ⟨a, b, hab⟩ := v
      obtain ⟨c, d, hcd⟩ := w
      simp only [blochVec] at hv
      have h0 := congrArg (fun p : EuclideanSpace ℝ (Fin 3) => p 0) hv
      have h1 := congrArg (fun p : EuclideanSpace ℝ (Fin 3) => p 1) hv
      have h2 := congrArg (fun p : EuclideanSpace ℝ (Fin 3) => p 2) hv
      simp only at h0 h1 h2
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons] at h0 h1 h2
      have hre : (a * (starRingEnd ℂ) b).re = (c * (starRingEnd ℂ) d).re := by linarith
      have him : (a * (starRingEnd ℂ) b).im = (c * (starRingEnd ℂ) d).im := by linarith
      have hprod : a * (starRingEnd ℂ) b = c * (starRingEnd ℂ) d := Complex.ext hre him
      obtain ⟨z, hz, hza, hzb⟩ := phase_of_bloch_eq hab hcd hprod h2
      exact Quotient.sound ⟨z, hz, hza, hzb⟩

/-- Every point of `S²` is the Bloch vector of some pure qubit state. -/
lemma exists_qubit_blochVec (x y z : ℝ) (h : x ^ 2 + y ^ 2 + z ^ 2 = 1) :
    ∃ v : Qubit, blochVec v = !₂[x, y, z] := by
  by_cases hz : z = -1
  · have hxy : x = 0 ∧ y = 0 := by
      constructor <;> nlinarith [sq_nonneg x, sq_nonneg y]
    exact ⟨⟨0, 1, by simp⟩, by simp [blochVec, hxy.1, hxy.2, hz]⟩
  · have hz1 : (0:ℝ) < 1 + z := by
      rcases lt_trichotomy (1 + z) 0 with hlt | heq | hgt
      · nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg (1 + z)]
      · exact absurd (by linarith : z = -1) hz
      · exact hgt
    set r := Real.sqrt ((1 + z) / 2) with hrdef
    have hr2 : r ^ 2 = (1 + z) / 2 := Real.sq_sqrt (by linarith)
    have hr0 : 0 < r := Real.sqrt_pos.mpr (by linarith)
    refine ⟨⟨⟨r, 0⟩, ⟨x / (2 * r), -(y / (2 * r))⟩, ?_⟩, ?_⟩
    · simp only [Complex.normSq_apply]
      field_simp
      nlinarith [hr2, h]
    · have hA : 2 * ((⟨r, 0⟩ : ℂ) * (starRingEnd ℂ) (⟨x / (2 * r), -(y / (2 * r))⟩ : ℂ)).re = x := by
        simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
        field_simp; ring
      have hB : 2 * ((⟨r, 0⟩ : ℂ) * (starRingEnd ℂ) (⟨x / (2 * r), -(y / (2 * r))⟩ : ℂ)).im = y := by
        simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
        field_simp; ring
      have hC : normSq (⟨r, 0⟩ : ℂ) - normSq (⟨x / (2 * r), -(y / (2 * r))⟩ : ℂ) = z := by
        simp only [Complex.normSq_apply]
        field_simp
        nlinarith [hr2, h]
      simp only [blochVec, hA, hB, hC]

lemma bloch_surjective : Function.Surjective bloch := by
  rintro ⟨p, hp⟩
  have hnorm : ‖p‖ = 1 := by simpa using hp
  have hsum : (p 0) ^ 2 + (p 1) ^ 2 + (p 2) ^ 2 = 1 := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_three, Real.sqrt_eq_one] at hnorm
    simpa [Real.norm_eq_abs, sq_abs] using hnorm
  obtain ⟨v, hv⟩ := exists_qubit_blochVec (p 0) (p 1) (p 2) hsum
  refine ⟨Quotient.mk _ v, Subtype.ext ?_⟩
  show blochVec v = p
  rw [hv]
  ext i
  fin_cases i <;> simp

/-- **Bloch sphere bijection**: pure qubit states modulo global phase are in bijection
with the points of the two-sphere `S² ⊆ ℝ³`. -/
theorem bloch_sphere_bijection : Function.Bijective bloch :=
  ⟨bloch_injective, bloch_surjective⟩

/-- The resulting explicit bijection `PureState ≃ S²`. -/
noncomputable def blochEquiv : PureState ≃ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  Equiv.ofBijective bloch bloch_sphere_bijection

end QC

