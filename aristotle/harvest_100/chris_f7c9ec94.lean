/-
/-!
# Bloch Sphere Bijection
Category: Quantum Computing
Target: QC.bloch_sphere_bijection
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/
import Mathlib

/-!
# Bloch Sphere Bijection
Category: Quantum Computing
Target: QC.bloch_sphere_bijection
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000

namespace QC

open Complex

/-- A pure qubit state: a unit vector in `ℂ²`. -/
def Qubit : Type := {v : ℂ × ℂ // normSq v.1 + normSq v.2 = 1}

/-- Two qubit states are equivalent when they differ by a global phase. -/
def PhaseRel (v w : Qubit) : Prop :=
  ∃ z : ℂ, normSq z = 1 ∧ w.val.1 = z * v.val.1 ∧ w.val.2 = z * v.val.2

lemma phaseRel_refl (v : Qubit) : PhaseRel v v :=
  ⟨1, by simp, by simp, by simp⟩

lemma phaseRel_symm {v w : Qubit} (h : PhaseRel v w) : PhaseRel w v := by
  obtain ⟨z, hz, h1, h2⟩ := h
  have hz0 : z ≠ 0 := by
    intro h0; rw [h0] at hz; simp at hz
  refine ⟨z⁻¹, ?_, ?_, ?_⟩
  · rw [map_inv₀, hz]; norm_num
  · rw [h1, ← mul_assoc, inv_mul_cancel₀ hz0, one_mul]
  · rw [h2, ← mul_assoc, inv_mul_cancel₀ hz0, one_mul]

lemma phaseRel_trans {u v w : Qubit} (h1 : PhaseRel u v) (h2 : PhaseRel v w) :
    PhaseRel u w := by
  obtain ⟨z, hz, hz1, hz2⟩ := h1
  obtain ⟨y, hy, hy1, hy2⟩ := h2
  exact ⟨y * z, by rw [map_mul, hy, hz]; norm_num,
    by rw [hy1, hz1, mul_assoc], by rw [hy2, hz2, mul_assoc]⟩

instance qubitSetoid : Setoid Qubit where
  r := PhaseRel
  iseqv := ⟨phaseRel_refl, phaseRel_symm, phaseRel_trans⟩

/-- Pure qubit states modulo global phase. -/
def PureState : Type := Quotient qubitSetoid

/-- The unit 2-sphere `S² ⊆ ℝ³`. -/
def Sphere2 : Type := {p : ℝ × ℝ × ℝ // p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 = 1}

lemma bloch_norm (a b : ℂ) (h : normSq a + normSq b = 1) :
    (2 * ((starRingEnd ℂ) a * b).re) ^ 2 + (2 * ((starRingEnd ℂ) a * b).im) ^ 2
      + (normSq a - normSq b) ^ 2 = 1 := by
  have key : (2 * ((starRingEnd ℂ) a * b).re) ^ 2 + (2 * ((starRingEnd ℂ) a * b).im) ^ 2
      + (normSq a - normSq b) ^ 2 = (normSq a + normSq b) ^ 2 := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.normSq_apply]
    ring
  rw [key, h]; norm_num

/-- The Bloch vector of a qubit state. -/
def blochVec (v : Qubit) : Sphere2 :=
  ⟨(2 * ((starRingEnd ℂ) v.val.1 * v.val.2).re,
    2 * ((starRingEnd ℂ) v.val.1 * v.val.2).im,
    normSq v.val.1 - normSq v.val.2), bloch_norm v.val.1 v.val.2 v.2⟩

/-- A unit-modulus scalar satisfies `conj z * z = 1`. -/
lemma conj_mul_self_of_normSq_one {z : ℂ} (hz : normSq z = 1) :
    (starRingEnd ℂ) z * z = 1 := by
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im, Complex.normSq_apply] at hz ⊢ <;> linarith [hz]

lemma blochVec_respects : ∀ v w : Qubit, PhaseRel v w → blochVec v = blochVec w := by
  rintro ⟨⟨a, b⟩, hv⟩ ⟨⟨c, d⟩, hw⟩ ⟨z, hz, h1, h2⟩
  simp only at h1 h2
  subst h1
  subst h2
  have hzz : (starRingEnd ℂ) z * z = 1 := conj_mul_self_of_normSq_one hz
  have hprod : (starRingEnd ℂ) (z * a) * (z * b) = (starRingEnd ℂ) a * b := by
    rw [map_mul]
    linear_combination ((starRingEnd ℂ) a * b) * hzz
  have hna : normSq (z * a) = normSq a := by rw [map_mul, hz, one_mul]
  have hnb : normSq (z * b) = normSq b := by rw [map_mul, hz, one_mul]
  apply Subtype.ext
  simp only [blochVec, hprod, hna, hnb]

/-- The Bloch map on states modulo global phase. -/
def bloch : PureState → Sphere2 :=
  Quotient.lift blochVec (fun v w h => blochVec_respects v w h)

/-- The key algebraic step for injectivity: if two unit vectors have the same
inner-product data `conj a * b` and the same modulus data, the second components
agree after the phase rotation `c / a`. -/
lemma second_component_eq {a b c d : ℂ}
    (hac : normSq a = normSq c) (hcd : (starRingEnd ℂ) a * b = (starRingEnd ℂ) c * d)
    (ha : a ≠ 0) : d = (c / a) * b := by
  have hc : c ≠ 0 := by intro h; apply ha; rw [h] at hac; simpa using hac
  have hcc : (starRingEnd ℂ) c ≠ 0 := by simpa using hc
  have h1 : c * (starRingEnd ℂ) c = ((normSq c : ℝ) : ℂ) := Complex.mul_conj c
  have h2 : a * (starRingEnd ℂ) a = ((normSq a : ℝ) : ℂ) := Complex.mul_conj a
  have hacC : ((normSq a : ℝ) : ℂ) = ((normSq c : ℝ) : ℂ) := by rw [hac]
  have key : d * a = c * b := by
    apply mul_right_cancel₀ hcc
    linear_combination (-a) * hcd + b * h2 - b * h1 + b * hacC
  field_simp
  linear_combination key

/-- Qubit states with the same Bloch vector differ by a global phase. -/
lemma phaseRel_of_blochVec_eq {v w : Qubit} (h : blochVec v = blochVec w) : PhaseRel v w := by
  obtain ⟨⟨a, b⟩, hv⟩ := v
  obtain ⟨⟨c, d⟩, hw⟩ := w
  have h1 := congrArg (fun p : Sphere2 => p.val.1) h
  have h2 := congrArg (fun p : Sphere2 => p.val.2.1) h
  have h3 := congrArg (fun p : Sphere2 => p.val.2.2) h
  simp only [blochVec] at h1 h2 h3
  simp only at hv hw
  have hac : normSq a = normSq c := by linarith
  have hbd : normSq b = normSq d := by linarith
  have hcd : (starRingEnd ℂ) a * b = (starRingEnd ℂ) c * d :=
    Complex.ext (by linarith) (by linarith)
  by_cases ha : a = 0
  · have hc : c = 0 := by
      rw [ha] at hac
      simp only [map_zero] at hac
      exact Complex.normSq_eq_zero.mp hac.symm
    have hb : b ≠ 0 := by
      intro hb0
      rw [ha, hb0] at hv
      simp at hv
    refine ⟨d / b, ?_, ?_, ?_⟩
    · rw [map_div₀, hbd]
      have : normSq d ≠ 0 := by
        rw [← hbd]; simpa [Complex.normSq_eq_zero] using hb
      field_simp
    · simp [ha, hc]
    · field_simp
  · have hc : c ≠ 0 := by intro h0; apply ha; rw [h0] at hac; simpa using hac
    refine ⟨c / a, ?_, ?_, ?_⟩
    · rw [map_div₀, hac]
      have : normSq c ≠ 0 := by simpa [Complex.normSq_eq_zero] using hc
      field_simp
    · simp only
      field_simp
    · exact second_component_eq hac hcd ha

theorem bloch_injective : Function.Injective bloch := by
  intro q1 q2 h
  induction q1 using Quotient.inductionOn with
  | _ v =>
    induction q2 using Quotient.inductionOn with
    | _ w =>
      exact Quotient.sound (phaseRel_of_blochVec_eq h)

theorem bloch_surjective : Function.Surjective bloch := by
  rintro ⟨⟨x, y, z⟩, hs⟩
  simp only at hs
  by_cases hz : z = -1
  · have hx : x = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
    have hy : y = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
    refine ⟨Quotient.mk qubitSetoid ⟨(0, 1), by simp⟩, ?_⟩
    apply Subtype.ext
    simp [bloch, blochVec, hx, hy, hz]
  · have hz1 : -1 < z := by
      rcases lt_trichotomy z (-1) with h | h | h
      · nlinarith [sq_nonneg x, sq_nonneg y]
      · exact absurd h hz
      · exact h
    have hpos : (0:ℝ) < (1 + z) / 2 := by linarith
    set r : ℝ := Real.sqrt ((1 + z) / 2)
    have hrpos : 0 < r := Real.sqrt_pos.mpr hpos
    have hr2 : r * r = (1 + z) / 2 := Real.mul_self_sqrt hpos.le
    have hb : normSq (⟨x / (2 * r), y / (2 * r)⟩ : ℂ) = (1 - z) / 2 := by
      simp only [Complex.normSq_apply]
      have h2r : (2 * r) ≠ 0 := by positivity
      field_simp
      nlinarith [hr2, hs]
    have hunit : normSq ((r : ℝ) : ℂ) + normSq (⟨x / (2 * r), y / (2 * r)⟩ : ℂ) = 1 := by
      rw [hb]
      simp only [Complex.normSq_ofReal]
      rw [hr2]
      ring
    refine ⟨Quotient.mk qubitSetoid ⟨((r : ℂ), (⟨x / (2 * r), y / (2 * r)⟩ : ℂ)), hunit⟩, ?_⟩
    apply Subtype.ext
    have hrne : r ≠ 0 := ne_of_gt hrpos
    simp only [bloch, Quotient.lift_mk, blochVec, Complex.normSq_ofReal]
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
        Complex.ofReal_im]
      field_simp
      ring
    · simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
        Complex.ofReal_im]
      field_simp
      ring
    · simp only [hb, hr2]
      ring

/-- Pure qubit states modulo global phase biject with the points of the 2-sphere `S²`. -/
theorem bloch_sphere_bijection : Function.Bijective bloch :=
  ⟨bloch_injective, bloch_surjective⟩

/-- Sanity check: the state `|0⟩` maps to the north pole of the sphere. -/
lemma bloch_zero_state :
    bloch (Quotient.mk qubitSetoid ⟨(1, 0), by simp⟩) = ⟨(0, 0, 1), by norm_num⟩ := by
  apply Subtype.ext
  simp [bloch, blochVec]

/-- Sanity check: the state `|1⟩` maps to the south pole of the sphere. -/
lemma bloch_one_state :
    bloch (Quotient.mk qubitSetoid ⟨(0, 1), by simp⟩) = ⟨(0, 0, -1), by norm_num⟩ := by
  apply Subtype.ext
  simp [bloch, blochVec]

/-- The resulting explicit bijection `PureState ≃ S²`. -/
noncomputable def blochEquiv : PureState ≃ Sphere2 :=
  Equiv.ofBijective bloch bloch_sphere_bijection

end QC

