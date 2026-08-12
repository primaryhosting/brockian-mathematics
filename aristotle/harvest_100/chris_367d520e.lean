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

/-- A pure qubit state: a unit vector in `ℂ²`, recorded as a pair of amplitudes
`(a, b)` with `|a|² + |b|² = 1`. -/
def PureState : Type := {p : ℂ × ℂ // normSq p.1 + normSq p.2 = 1}

namespace PureState

/-- First amplitude of a pure state. -/
def a (p : PureState) : ℂ := p.1.1

/-- Second amplitude of a pure state. -/
def b (p : PureState) : ℂ := p.1.2

theorem norm_eq (p : PureState) : normSq p.a + normSq p.b = 1 := p.2

end PureState

/-- Two pure states are physically identical when they differ by a global phase. -/
def PhaseRel (p q : PureState) : Prop :=
  ∃ z : ℂ, ‖z‖ = 1 ∧ q.a = z * p.a ∧ q.b = z * p.b

theorem phaseRel_refl (p : PureState) : PhaseRel p p :=
  ⟨1, by simp, (one_mul _).symm, (one_mul _).symm⟩

theorem phaseRel_symm {p q : PureState} (h : PhaseRel p q) : PhaseRel q p := by
  obtain ⟨z, hz, ha, hb⟩ := h
  have hz0 : z ≠ 0 := by intro h0; rw [h0] at hz; simp at hz
  refine ⟨z⁻¹, by simp [hz], ?_, ?_⟩
  · rw [ha]; field_simp
  · rw [hb]; field_simp

theorem phaseRel_trans {p q r : PureState} (h1 : PhaseRel p q) (h2 : PhaseRel q r) :
    PhaseRel p r := by
  obtain ⟨z, hz, ha, hb⟩ := h1
  obtain ⟨w, hw, hc, hd⟩ := h2
  exact ⟨w * z, by simp [hz, hw], by rw [hc, ha]; ring, by rw [hd, hb]; ring⟩

/-- The setoid identifying pure states that differ by a global phase. -/
def phaseSetoid : Setoid PureState where
  r := PhaseRel
  iseqv := ⟨phaseRel_refl, phaseRel_symm, phaseRel_trans⟩

/-- The space of pure qubit states modulo global phase. -/
def Qubit : Type := Quotient phaseSetoid

/-- The 2-sphere `S² ⊆ ℝ³`. -/
abbrev Sphere2 : Set (EuclideanSpace ℝ (Fin 3)) := Metric.sphere 0 1

theorem mem_sphere2_iff (v : EuclideanSpace ℝ (Fin 3)) :
    v ∈ Sphere2 ↔ v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1 := by
  rw [mem_sphere_iff_norm, sub_zero, EuclideanSpace.norm_eq, Fin.sum_univ_three]
  simp only [Real.norm_eq_abs, sq_abs]
  constructor
  · intro h
    nlinarith [Real.sq_sqrt (by positivity : (0:ℝ) ≤ v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2), h]
  · intro h; rw [h]; simp

/-- The Bloch vector of a pure state `(a, b)`:
`(2 Re(conj a · b), 2 Im(conj a · b), |a|² - |b|²)`. -/
def blochVec (p : PureState) : EuclideanSpace ℝ (Fin 3) :=
  !₂[2 * ((starRingEnd ℂ) p.a * p.b).re,
     2 * ((starRingEnd ℂ) p.a * p.b).im,
     normSq p.a - normSq p.b]

theorem blochVec_apply_zero (p : PureState) :
    blochVec p 0 = 2 * ((starRingEnd ℂ) p.a * p.b).re := by simp [blochVec]

theorem blochVec_apply_one (p : PureState) :
    blochVec p 1 = 2 * ((starRingEnd ℂ) p.a * p.b).im := by simp [blochVec]

theorem blochVec_apply_two (p : PureState) :
    blochVec p 2 = normSq p.a - normSq p.b := by simp [blochVec]

theorem blochVec_mem (p : PureState) : blochVec p ∈ Sphere2 := by
  rw [mem_sphere2_iff, blochVec_apply_zero, blochVec_apply_one, blochVec_apply_two]
  have h := p.norm_eq
  simp only [normSq_apply, mul_re, mul_im, conj_re, conj_im] at h ⊢
  nlinarith [h, sq_nonneg (p.a.re * p.b.re + p.a.im * p.b.im)]

/-- The Bloch map on pure states, landing in `S²`. -/
def bloch (p : PureState) : Sphere2 := ⟨blochVec p, blochVec_mem p⟩

theorem bloch_phase_invariant {p q : PureState} (h : PhaseRel p q) : bloch p = bloch q := by
  obtain ⟨z, hz, ha, hb⟩ := h
  have hzz : normSq z = 1 := by
    rw [Complex.normSq_eq_norm_sq, hz]; norm_num
  have h0 : ((starRingEnd ℂ) q.a * q.b) = ((starRingEnd ℂ) p.a * p.b) := by
    rw [ha, hb, map_mul]
    have : (starRingEnd ℂ) z * z = 1 := by
      rw [← Complex.normSq_eq_conj_mul_self, hzz]; norm_num
    calc (starRingEnd ℂ) z * (starRingEnd ℂ) p.a * (z * p.b)
        = ((starRingEnd ℂ) z * z) * ((starRingEnd ℂ) p.a * p.b) := by ring
      _ = (starRingEnd ℂ) p.a * p.b := by rw [this, one_mul]
  have h1 : normSq q.a = normSq p.a := by rw [ha, map_mul, hzz, one_mul]
  have h2 : normSq q.b = normSq p.b := by rw [hb, map_mul, hzz, one_mul]
  simp only [bloch, blochVec, h0, h1, h2]

/-- The Bloch map descends to the quotient by global phase. -/
def blochQuot : Qubit → Sphere2 :=
  Quotient.lift bloch (fun _ _ h => bloch_phase_invariant h)

theorem blochQuot_mk (p : PureState) : blochQuot (Quotient.mk phaseSetoid p) = bloch p := rfl

theorem norm_eq_of_normSq_eq {u v : ℂ} (h : normSq u = normSq v) : ‖u‖ = ‖v‖ := by
  have h1 := Complex.normSq_eq_norm_sq u
  have h2 := Complex.normSq_eq_norm_sq v
  nlinarith [norm_nonneg u, norm_nonneg v]

theorem bloch_injective_mod_phase {p q : PureState} (h : bloch p = bloch q) : PhaseRel p q := by
  have hv : blochVec p = blochVec q := congrArg Subtype.val h
  have e0 : 2 * ((starRingEnd ℂ) p.a * p.b).re = 2 * ((starRingEnd ℂ) q.a * q.b).re := by
    rw [← blochVec_apply_zero, ← blochVec_apply_zero, hv]
  have e1 : 2 * ((starRingEnd ℂ) p.a * p.b).im = 2 * ((starRingEnd ℂ) q.a * q.b).im := by
    rw [← blochVec_apply_one, ← blochVec_apply_one, hv]
  have e2 : normSq p.a - normSq p.b = normSq q.a - normSq q.b := by
    rw [← blochVec_apply_two, ← blochVec_apply_two, hv]
  have hprod : (starRingEnd ℂ) p.a * p.b = (starRingEnd ℂ) q.a * q.b :=
    Complex.ext (by linarith) (by linarith)
  have hp := p.norm_eq
  have hq := q.norm_eq
  have hna : normSq p.a = normSq q.a := by linarith
  have hnb : normSq p.b = normSq q.b := by linarith
  by_cases hpa : p.a = 0
  · have hqa : q.a = 0 := by
      have : normSq q.a = 0 := by rw [← hna, hpa]; simp
      exact normSq_eq_zero.mp this
    have hpb : p.b ≠ 0 := by
      intro h0
      rw [hpa, h0] at hp; simp at hp
    refine ⟨q.b / p.b, ?_, ?_, ?_⟩
    · rw [norm_div, ← norm_eq_of_normSq_eq hnb]
      exact div_self (by simpa using hpb)
    · rw [hpa, hqa, mul_zero]
    · field_simp
  · have hqa : q.a ≠ 0 := by
      intro h0
      rw [h0] at hna; simp at hna; exact hpa hna
    have hcpa : (starRingEnd ℂ) p.a ≠ 0 := by simpa using hpa
    have key : q.a * p.b = p.a * q.b := by
      have h5 : (starRingEnd ℂ) p.a * (q.a * p.b) = (starRingEnd ℂ) p.a * (p.a * q.b) := by
        calc (starRingEnd ℂ) p.a * (q.a * p.b)
            = q.a * ((starRingEnd ℂ) p.a * p.b) := by ring
          _ = q.a * ((starRingEnd ℂ) q.a * q.b) := by rw [hprod]
          _ = ((starRingEnd ℂ) q.a * q.a) * q.b := by ring
          _ = (normSq q.a : ℂ) * q.b := by rw [← Complex.normSq_eq_conj_mul_self]
          _ = (normSq p.a : ℂ) * q.b := by rw [hna]
          _ = ((starRingEnd ℂ) p.a * p.a) * q.b := by rw [← Complex.normSq_eq_conj_mul_self]
          _ = (starRingEnd ℂ) p.a * (p.a * q.b) := by ring
      exact mul_left_cancel₀ hcpa h5
    refine ⟨q.a / p.a, ?_, ?_, ?_⟩
    · rw [norm_div, ← norm_eq_of_normSq_eq hna]
      exact div_self (by simpa using hpa)
    · field_simp
    · field_simp
      linear_combination -key

theorem blochQuot_injective : Function.Injective blochQuot := by
  intro x y h
  induction x using Quotient.inductionOn with
  | h p =>
    induction y using Quotient.inductionOn with
    | h q =>
      exact Quotient.sound (bloch_injective_mod_phase h)

theorem euclidean3_ext {u w : EuclideanSpace ℝ (Fin 3)} (h0 : u 0 = w 0) (h1 : u 1 = w 1)
    (h2 : u 2 = w 2) : u = w := by
  ext i; fin_cases i <;> assumption

theorem bloch_surjective : Function.Surjective bloch := by
  rintro ⟨v, hv⟩
  rw [mem_sphere2_iff] at hv
  by_cases hz : v 2 = -1
  · have hx : v 0 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
    have hy : v 1 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
    refine ⟨⟨(0, 1), by simp⟩, ?_⟩
    apply Subtype.ext
    show blochVec _ = v
    refine euclidean3_ext ?_ ?_ ?_
    · rw [blochVec_apply_zero, hx]
      show 2 * ((starRingEnd ℂ) (0 : ℂ) * (1 : ℂ)).re = 0
      simp
    · rw [blochVec_apply_one, hy]
      show 2 * ((starRingEnd ℂ) (0 : ℂ) * (1 : ℂ)).im = 0
      simp
    · rw [blochVec_apply_two, hz]
      show normSq (0 : ℂ) - normSq (1 : ℂ) = -1
      simp
  · have hzgt : -1 < v 2 := by
      rcases lt_or_ge (v 2) (-1) with h | h
      · nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
      · exact lt_of_le_of_ne h (Ne.symm hz)
    obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = Real.sqrt ((1 + v 2) / 2) := ⟨_, rfl⟩
    have hrpos : 0 < r := by rw [hrdef]; exact Real.sqrt_pos.mpr (by linarith)
    have hrne : r ≠ 0 := ne_of_gt hrpos
    have hr2 : r ^ 2 = (1 + v 2) / 2 := by rw [hrdef]; exact Real.sq_sqrt (by linarith)
    obtain ⟨A, hA⟩ : ∃ A : ℂ, A = (r : ℂ) := ⟨_, rfl⟩
    obtain ⟨B, hB⟩ : ∃ B : ℂ,
        B = ((v 0 / (2 * r) : ℝ) : ℂ) + ((v 1 / (2 * r) : ℝ) : ℂ) * Complex.I := ⟨_, rfl⟩
    have hAre : A.re = r := by rw [hA]; simp
    have hAim : A.im = 0 := by rw [hA]; simp
    have hBre : B.re = v 0 / (2 * r) := by
      rw [hB]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      ring
    have hBim : B.im = v 1 / (2 * r) := by
      rw [hB]
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_re, Complex.I_im]
      ring
    have hnA : normSq A = r ^ 2 := by rw [normSq_apply, hAre, hAim]; ring
    have hnB : normSq B = (v 0 ^ 2 + v 1 ^ 2) / (4 * r ^ 2) := by
      rw [normSq_apply, hBre, hBim]; field_simp; ring
    have hsq : v 0 ^ 2 + v 1 ^ 2 = 1 - v 2 ^ 2 := by linarith
    have hsum : normSq A + normSq B = 1 := by
      rw [hnA, hnB, hsq, hr2]
      have hden : (1 : ℝ) + v 2 ≠ 0 := by linarith
      field_simp
      ring
    refine ⟨⟨(A, B), hsum⟩, ?_⟩
    apply Subtype.ext
    show blochVec _ = v
    refine euclidean3_ext ?_ ?_ ?_
    · rw [blochVec_apply_zero]
      show 2 * ((starRingEnd ℂ) A * B).re = v 0
      rw [Complex.mul_re, Complex.conj_re, Complex.conj_im, hAre, hAim, hBre, hBim]
      field_simp
      ring
    · rw [blochVec_apply_one]
      show 2 * ((starRingEnd ℂ) A * B).im = v 1
      rw [Complex.mul_im, Complex.conj_re, Complex.conj_im, hAre, hAim, hBre, hBim]
      field_simp
      ring
    · rw [blochVec_apply_two]
      show normSq A - normSq B = v 2
      rw [hnA, hnB, hsq, hr2]
      have hden : (1 : ℝ) + v 2 ≠ 0 := by linarith
      field_simp
      ring

theorem blochQuot_surjective : Function.Surjective blochQuot := by
  intro v
  obtain ⟨p, hp⟩ := bloch_surjective v
  exact ⟨Quotient.mk phaseSetoid p, hp⟩

/-- **Bloch sphere bijection**: pure qubit states modulo global phase are in bijection
with the points of the 2-sphere `S² ⊆ ℝ³`, via the Bloch map. -/
theorem bloch_sphere_bijection : Function.Bijective blochQuot :=
  ⟨blochQuot_injective, blochQuot_surjective⟩

/-- The induced equivalence between the projective qubit space and `S²`. -/
noncomputable def blochEquiv : Qubit ≃ Sphere2 :=
  Equiv.ofBijective blochQuot bloch_sphere_bijection

end QC

