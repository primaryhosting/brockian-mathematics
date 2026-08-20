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
def QubitState : Type := {v : Fin 2 → ℂ // ‖v 0‖ ^ 2 + ‖v 1‖ ^ 2 = 1}

/-- Two qubit states are identified when they differ by a global phase. -/
instance qubitSetoid : Setoid QubitState where
  r v w := ∃ z : ℂ, ‖z‖ = 1 ∧ ∀ i, w.1 i = z * v.1 i
  iseqv := by
    constructor
    · intro v; exact ⟨1, by simp, by simp⟩
    · rintro v w ⟨z, hz, h⟩
      refine ⟨z⁻¹, ?_, ?_⟩
      · simp [hz]
      · intro i
        have hz0 : z ≠ 0 := by
          intro h0; rw [h0] at hz; simp at hz
        rw [h i, ← mul_assoc, inv_mul_cancel₀ hz0, one_mul]
    · rintro u v w ⟨z, hz, h⟩ ⟨y, hy, h'⟩
      refine ⟨y * z, by simp [hy, hz], ?_⟩
      intro i
      rw [h' i, h i]; ring

/-- Pure qubit states modulo global phase. -/
def PureState : Type := Quotient qubitSetoid

/-- The 2-sphere `S² ⊆ ℝ³`. -/
def Sphere2 : Type := {p : Fin 3 → ℝ // p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 = 1}

@[ext] theorem Sphere2.ext {p q : Sphere2} (h : ∀ i, p.1 i = q.1 i) : p = q :=
  Subtype.ext (funext h)

/-- The Bloch vector of a unit vector in `ℂ²`. -/
noncomputable def blochRaw (v : QubitState) : Sphere2 :=
  ⟨![2 * ((starRingEnd ℂ) (v.1 0) * v.1 1).re,
     2 * ((starRingEnd ℂ) (v.1 0) * v.1 1).im,
     ‖v.1 0‖ ^ 2 - ‖v.1 1‖ ^ 2], by
    obtain ⟨v, hv⟩ := v
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    simp only [Complex.sq_norm] at hv ⊢
    simp only [Complex.mul_re, Complex.mul_im, Complex.normSq_apply, Complex.conj_re,
      Complex.conj_im] at hv ⊢
    nlinarith [hv, sq_nonneg ((v 0).re), sq_nonneg ((v 0).im), sq_nonneg ((v 1).re),
      sq_nonneg ((v 1).im)]⟩

theorem blochRaw_respects (v w : QubitState) (h : v ≈ w) : blochRaw v = blochRaw w := by
  obtain ⟨z, hz, hvw⟩ := h
  have hz' : Complex.normSq z = 1 := by
    rw [← Complex.sq_norm, hz]; norm_num
  have hzz : (starRingEnd ℂ) z * z = 1 := by
    rw [mul_comm, Complex.mul_conj, hz']; norm_num
  have hprod : (starRingEnd ℂ) (w.1 0) * w.1 1 = (starRingEnd ℂ) (v.1 0) * v.1 1 := by
    rw [hvw 0, hvw 1, map_mul]
    linear_combination ((starRingEnd ℂ) (v.1 0) * v.1 1) * hzz
  have hn0 : ‖w.1 0‖ = ‖v.1 0‖ := by rw [hvw 0, norm_mul, hz, one_mul]
  have hn1 : ‖w.1 1‖ = ‖v.1 1‖ := by rw [hvw 1, norm_mul, hz, one_mul]
  apply Sphere2.ext
  intro i
  fin_cases i <;>
    simp only [blochRaw, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.zero_eta, Fin.mk_one, Fin.isValue, hprod, hn0, hn1]

/-- The Bloch map from pure states modulo phase to the 2-sphere. -/
noncomputable def bloch : PureState → Sphere2 := Quotient.lift blochRaw blochRaw_respects

@[simp] theorem bloch_mk (v : QubitState) : bloch (Quotient.mk qubitSetoid v) = blochRaw v := rfl

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

theorem bloch_surjective : Function.Surjective bloch := by
  rintro ⟨p, hp⟩
  by_cases hz : p 2 = -1
  · refine ⟨Quotient.mk qubitSetoid ⟨![0, 1], by norm_num⟩, ?_⟩
    rw [bloch_mk]
    apply Sphere2.ext
    intro i
    have hxy : p 0 ^ 2 + p 1 ^ 2 = 0 := by rw [hz] at hp; nlinarith
    have hx : p 0 = 0 := by nlinarith [sq_nonneg (p 0), sq_nonneg (p 1)]
    have hy : p 1 = 0 := by nlinarith [sq_nonneg (p 0), sq_nonneg (p 1)]
    fin_cases i <;> simp [blochRaw, hx, hy, hz]
  · -- p 2 ≠ -1, so 1 + p 2 > 0
    have hple : p 2 ^ 2 ≤ 1 := by nlinarith [sq_nonneg (p 0), sq_nonneg (p 1)]
    have hge : -1 ≤ p 2 := by nlinarith
    have hpos : 0 < 1 + p 2 := by
      rcases lt_or_eq_of_le hge with h | h
      · linarith
      · exact absurd h.symm hz
    set a : ℝ := Real.sqrt ((1 + p 2) / 2) with ha
    have ha2 : a ^ 2 = (1 + p 2) / 2 := Real.sq_sqrt (by positivity)
    have hapos : 0 < a := Real.sqrt_pos.mpr (by positivity)
    refine ⟨Quotient.mk qubitSetoid ⟨![(a : ℂ), (p 0 / (2 * a) : ℝ) + (p 1 / (2 * a) : ℝ) * Complex.I], ?_⟩, ?_⟩
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [Complex.sq_norm, Complex.sq_norm]
      simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      field_simp
      nlinarith [hp, ha2, hapos]
    · rw [bloch_mk]
      apply Sphere2.ext
      intro i
      have hane : (a : ℝ) ≠ 0 := ne_of_gt hapos
      have hprod : (starRingEnd ℂ) ((a : ℝ) : ℂ) *
          ((((p 0 / (2 * a) : ℝ)) : ℂ) + (((p 1 / (2 * a) : ℝ)) : ℂ) * Complex.I) =
          (((p 0 / 2 : ℝ)) : ℂ) + (((p 1 / 2 : ℝ)) : ℂ) * Complex.I := by
        have hanec : ((a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hane
        rw [Complex.conj_ofReal]
        push_cast
        field_simp
      have hnb : ‖(((p 0 / (2 * a) : ℝ)) : ℂ) + (((p 1 / (2 * a) : ℝ)) : ℂ) * Complex.I‖ ^ 2
          = (1 - p 2) / 2 := by
        rw [Complex.sq_norm]
        simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
          Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
        field_simp
        nlinarith [hp, ha2, hapos]
      have hna : ‖((a : ℝ) : ℂ)‖ ^ 2 = (1 + p 2) / 2 := by
        rw [Complex.sq_norm]
        simp only [Complex.normSq_apply, Complex.ofReal_re, Complex.ofReal_im]
        nlinarith [ha2]
      fin_cases i <;>
        simp only [blochRaw, Matrix.cons_val_zero, Matrix.cons_val_one,
          Fin.zero_eta, Fin.mk_one, Fin.isValue,
          hprod, hnb, hna, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      · ring
      · ring
      · show (1 + p 2) / 2 - (1 - p 2) / 2 = p 2
        ring

/-- **Bloch sphere bijection**: pure qubit states modulo global phase are in bijection with
the points of the 2-sphere `S²`. -/
theorem bloch_sphere_bijection : Function.Bijective bloch :=
  ⟨bloch_injective, bloch_surjective⟩

end QC

