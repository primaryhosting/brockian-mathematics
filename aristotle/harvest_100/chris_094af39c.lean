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

/-! ## Pure qubit states -/

/-- A pure state of a single qubit: a unit vector `a|0⟩ + b|1⟩` in `ℂ²`. -/
structure Qubit where
  /-- amplitude of `|0⟩` -/
  a : ℂ
  /-- amplitude of `|1⟩` -/
  b : ℂ
  /-- normalization -/
  norm_eq : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1

namespace Qubit

/-- Two qubit states are physically identical when they differ by a global phase. -/
def PhaseRel (v w : Qubit) : Prop :=
  ∃ z : ℂ, ‖z‖ = 1 ∧ w.a = z * v.a ∧ w.b = z * v.b

theorem phaseRel_refl (v : Qubit) : PhaseRel v v :=
  ⟨1, by simp, by simp, by simp⟩

theorem phaseRel_symm {v w : Qubit} (h : PhaseRel v w) : PhaseRel w v := by
  obtain ⟨z, hz, ha, hb⟩ := h
  have hz0 : z ≠ 0 := by
    intro h0; rw [h0] at hz; simp at hz
  refine ⟨z⁻¹, by simp [hz], ?_, ?_⟩
  · rw [ha, ← mul_assoc, inv_mul_cancel₀ hz0, one_mul]
  · rw [hb, ← mul_assoc, inv_mul_cancel₀ hz0, one_mul]

theorem phaseRel_trans {u v w : Qubit} (h₁ : PhaseRel u v) (h₂ : PhaseRel v w) :
    PhaseRel u w := by
  obtain ⟨z, hz, ha, hb⟩ := h₁
  obtain ⟨z', hz', ha', hb'⟩ := h₂
  exact ⟨z' * z, by simp [hz, hz'], by rw [ha', ha, mul_assoc], by rw [hb', hb, mul_assoc]⟩

instance phaseSetoid : Setoid Qubit where
  r := PhaseRel
  iseqv := ⟨phaseRel_refl, phaseRel_symm, phaseRel_trans⟩

theorem norm_a_sq (v : Qubit) : ‖v.a‖ ^ 2 = v.a.re ^ 2 + v.a.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

theorem norm_b_sq (v : Qubit) : ‖v.b‖ ^ 2 = v.b.re ^ 2 + v.b.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

end Qubit

/-- Pure qubit states modulo global phase. -/
abbrev PureState : Type := Quotient Qubit.phaseSetoid

/-- The two-sphere `S² ⊆ ℝ³`. -/
abbrev Sphere2 : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

/-! ## The Bloch vector -/

/-- First Bloch coordinate `⟨ψ|σₓ|ψ⟩`. -/
noncomputable def blochX (v : Qubit) : ℝ := 2 * ((starRingEnd ℂ) v.a * v.b).re

/-- Second Bloch coordinate `⟨ψ|σ_y|ψ⟩`. -/
noncomputable def blochY (v : Qubit) : ℝ := 2 * ((starRingEnd ℂ) v.a * v.b).im

/-- Third Bloch coordinate `⟨ψ|σ_z|ψ⟩`. -/
noncomputable def blochZ (v : Qubit) : ℝ := ‖v.a‖ ^ 2 - ‖v.b‖ ^ 2

theorem blochX_eq (v : Qubit) : blochX v = 2 * (v.a.re * v.b.re + v.a.im * v.b.im) := by
  simp only [blochX, Complex.mul_re, Complex.conj_re, Complex.conj_im]; ring

theorem blochY_eq (v : Qubit) : blochY v = 2 * (v.a.re * v.b.im - v.a.im * v.b.re) := by
  simp only [blochY, Complex.mul_im, Complex.conj_re, Complex.conj_im]; ring

theorem bloch_mem_sphere (v : Qubit) :
    (!₂[blochX v, blochY v, blochZ v] : EuclideanSpace ℝ (Fin 3)) ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  have hs : v.a.re ^ 2 + v.a.im ^ 2 + (v.b.re ^ 2 + v.b.im ^ 2) = 1 := by
    have := v.norm_eq
    rw [Qubit.norm_a_sq, Qubit.norm_b_sq] at this
    linarith
  have key : blochX v ^ 2 + blochY v ^ 2 + blochZ v ^ 2 = 1 := by
    rw [blochX_eq, blochY_eq, blochZ, Qubit.norm_a_sq, Qubit.norm_b_sq]
    nlinarith [hs]
  simp only [Metric.mem_sphere, dist_zero_right, EuclideanSpace.norm_eq, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Real.norm_eq_abs, sq_abs]
  rw [key, Real.sqrt_one]

/-- The Bloch vector of a pure qubit state, as a point of `S²`. -/
noncomputable def blochMap (v : Qubit) : Sphere2 :=
  ⟨!₂[blochX v, blochY v, blochZ v], bloch_mem_sphere v⟩

theorem blochMap_eq_iff (v w : Qubit) :
    blochMap v = blochMap w ↔ blochX v = blochX w ∧ blochY v = blochY w ∧ blochZ v = blochZ w := by
  constructor
  · intro h
    have h' : (!₂[blochX v, blochY v, blochZ v] : EuclideanSpace ℝ (Fin 3))
        = !₂[blochX w, blochY w, blochZ w] := congrArg Subtype.val h
    refine ⟨?_, ?_, ?_⟩
    · simpa using congrArg (fun p : EuclideanSpace ℝ (Fin 3) => p 0) h'
    · simpa using congrArg (fun p : EuclideanSpace ℝ (Fin 3) => p 1) h'
    · simpa using congrArg (fun p : EuclideanSpace ℝ (Fin 3) => p 2) h'
  · rintro ⟨h1, h2, h3⟩
    simp [blochMap, h1, h2, h3]

theorem blochMap_phase_invariant {v w : Qubit} (h : Qubit.PhaseRel v w) :
    blochMap v = blochMap w := by
  obtain ⟨z, hz, ha, hb⟩ := h
  have hzz : (starRingEnd ℂ) z * z = 1 := by
    rw [Complex.conj_mul']
    norm_cast
    rw [hz]; norm_num
  rw [blochMap_eq_iff]
  have hxy : (starRingEnd ℂ) w.a * w.b = (starRingEnd ℂ) v.a * v.b := by
    rw [ha, hb, map_mul]
    calc (starRingEnd ℂ) z * (starRingEnd ℂ) v.a * (z * v.b)
        = ((starRingEnd ℂ) z * z) * ((starRingEnd ℂ) v.a * v.b) := by ring
      _ = (starRingEnd ℂ) v.a * v.b := by rw [hzz, one_mul]
  have hna : ‖w.a‖ = ‖v.a‖ := by rw [ha, norm_mul, hz, one_mul]
  have hnb : ‖w.b‖ = ‖v.b‖ := by rw [hb, norm_mul, hz, one_mul]
  refine ⟨?_, ?_, ?_⟩
  · rw [blochX, blochX, hxy]
  · rw [blochY, blochY, hxy]
  · rw [blochZ, blochZ, hna, hnb]

/-- The Bloch map on states modulo global phase. -/
noncomputable def blochQuot : PureState → Sphere2 :=
  Quotient.lift blochMap (fun _ _ h => blochMap_phase_invariant h)

@[simp] theorem blochQuot_mk (v : Qubit) : blochQuot (Quotient.mk _ v) = blochMap v := rfl

/-! ## Injectivity -/

theorem blochMap_inj {v w : Qubit} (h : blochMap v = blochMap w) : Qubit.PhaseRel v w := by
  rw [blochMap_eq_iff] at h
  obtain ⟨hx, hy, hz⟩ := h
  -- equal off-diagonal products
  have hprod : (starRingEnd ℂ) v.a * v.b = (starRingEnd ℂ) w.a * w.b := by
    apply Complex.ext
    · have := hx; rw [blochX, blochX] at this; linarith
    · have := hy; rw [blochY, blochY] at this; linarith
  -- equal moduli
  have hz' : ‖v.a‖ ^ 2 - ‖v.b‖ ^ 2 = ‖w.a‖ ^ 2 - ‖w.b‖ ^ 2 := hz
  have hsa : ‖v.a‖ ^ 2 = ‖w.a‖ ^ 2 := by
    have h1 := v.norm_eq; have h2 := w.norm_eq; linarith
  have hsb : ‖v.b‖ ^ 2 = ‖w.b‖ ^ 2 := by
    have h1 := v.norm_eq; have h2 := w.norm_eq; linarith
  have hna : ‖v.a‖ = ‖w.a‖ := by
    nlinarith [norm_nonneg v.a, norm_nonneg w.a]
  have hnb : ‖v.b‖ = ‖w.b‖ := by
    nlinarith [norm_nonneg v.b, norm_nonneg w.b]
  by_cases hva : v.a = 0
  · -- then both first amplitudes vanish and the second ones are unit
    have hwa : w.a = 0 := by
      have : ‖w.a‖ = 0 := by rw [← hna, hva, norm_zero]
      simpa using this
    have hvb : v.b ≠ 0 := by
      intro h0
      have := v.norm_eq
      rw [hva, h0] at this
      simp at this
    refine ⟨w.b / v.b, ?_, ?_, ?_⟩
    · have hbne : ‖w.b‖ ≠ 0 := by
        rw [← hnb]; simpa using hvb
      rw [norm_div, hnb, div_self hbne]
    · rw [hva, hwa, mul_zero]
    · field_simp
  · refine ⟨w.a / v.a, ?_, ?_, ?_⟩
    · rw [norm_div, hna]
      have : ‖w.a‖ ≠ 0 := by
        rw [← hna]; simpa using hva
      field_simp
    · field_simp
    · -- key cross relation: w.a * v.b = v.a * w.b
      have hcross : w.a * v.b = v.a * w.b := by
        have hmul : w.a * ((starRingEnd ℂ) v.a * v.b) = w.a * ((starRingEnd ℂ) w.a * w.b) := by
          rw [hprod]
        have h1 : w.a * ((starRingEnd ℂ) w.a * w.b) = ((‖w.a‖ : ℂ) ^ 2) * w.b := by
          rw [← mul_assoc, Complex.mul_conj']
        have h2 : w.a * ((starRingEnd ℂ) v.a * v.b) = (starRingEnd ℂ) v.a * (w.a * v.b) := by
          ring
        have h3 : ((‖w.a‖ : ℂ) ^ 2) * w.b = ((‖v.a‖ : ℂ) ^ 2) * w.b := by rw [hna]
        have h4 : ((‖v.a‖ : ℂ) ^ 2) * w.b = (starRingEnd ℂ) v.a * (v.a * w.b) := by
          rw [← Complex.conj_mul']
          ring
        have hca : (starRingEnd ℂ) v.a ≠ 0 := by
          simpa using hva
        rw [h2, h1, h3, h4] at hmul
        exact mul_left_cancel₀ hca hmul
      field_simp
      linear_combination -hcross

/-! ## Surjectivity -/

theorem blochMap_surj (p : Sphere2) : ∃ v : Qubit, blochMap v = p := by
  set x : ℝ := (p : EuclideanSpace ℝ (Fin 3)) 0 with hxdef
  set y : ℝ := (p : EuclideanSpace ℝ (Fin 3)) 1 with hydef
  set z : ℝ := (p : EuclideanSpace ℝ (Fin 3)) 2 with hzdef
  have hp : x ^ 2 + y ^ 2 + z ^ 2 = 1 := by
    have hp' := p.2
    simp only [Metric.mem_sphere, dist_zero_right, EuclideanSpace.norm_eq,
      Fin.sum_univ_three, Real.norm_eq_abs, sq_abs] at hp'
    nlinarith [Real.sq_sqrt (by positivity : (0:ℝ) ≤ x ^ 2 + y ^ 2 + z ^ 2), hp']
  have hpp : (!₂[x, y, z] : EuclideanSpace ℝ (Fin 3)) = (p : EuclideanSpace ℝ (Fin 3)) := by
    ext i; fin_cases i <;> simp [hxdef, hydef, hzdef]
  by_cases hz1 : z = -1
  · refine ⟨⟨0, 1, by norm_num⟩, ?_⟩
    have hx0 : x = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
    have hy0 : y = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
    apply Subtype.ext
    rw [← hpp, hx0, hy0, hz1]
    simp [blochMap, blochX, blochY, blochZ]
  · have hzge : -1 < z := by
      have hz2 : -1 ≤ z := by nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg (z + 1)]
      exact lt_of_le_of_ne hz2 (Ne.symm hz1)
    have hpos : 0 < (1 + z) / 2 := by linarith
    set r : ℝ := Real.sqrt ((1 + z) / 2) with hrdef
    have hr0 : 0 < r := Real.sqrt_pos.mpr hpos
    have hr2 : r ^ 2 = (1 + z) / 2 := Real.sq_sqrt hpos.le
    have hxy : x ^ 2 + y ^ 2 = 1 - z ^ 2 := by linarith
    have hnorm : ‖(r : ℂ)‖ ^ 2 + ‖(⟨x / (2 * r), y / (2 * r)⟩ : ℂ)‖ ^ 2 = 1 := by
      rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
      simp only [Complex.ofReal_re, Complex.ofReal_im]
      field_simp
      nlinarith [hr2, hxy]
    refine ⟨⟨(r : ℂ), ⟨x / (2 * r), y / (2 * r)⟩, hnorm⟩, ?_⟩
    set v : Qubit := ⟨(r : ℂ), ⟨x / (2 * r), y / (2 * r)⟩, hnorm⟩ with hv
    have hva : v.a = (r : ℂ) := rfl
    have hvb : v.b = (⟨x / (2 * r), y / (2 * r)⟩ : ℂ) := rfl
    have hX : blochX v = x := by
      rw [blochX_eq, hva, hvb]
      simp only [Complex.ofReal_re, Complex.ofReal_im]
      field_simp
      ring
    have hY : blochY v = y := by
      rw [blochY_eq, hva, hvb]
      simp only [Complex.ofReal_re, Complex.ofReal_im]
      field_simp
      ring
    have hZ : blochZ v = z := by
      rw [blochZ, hva, hvb, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
        Complex.normSq_apply]
      simp only [Complex.ofReal_re, Complex.ofReal_im]
      field_simp
      nlinarith [hr2, hxy]
    apply Subtype.ext
    rw [← hpp]
    show (!₂[blochX v, blochY v, blochZ v] : EuclideanSpace ℝ (Fin 3)) = !₂[x, y, z]
    rw [hX, hY, hZ]

theorem bloch_sphere_bijection : Function.Bijective blochQuot := by
  constructor
  · intro P Q
    refine Quotient.inductionOn₂ P Q ?_
    intro v w h
    exact Quotient.sound (blochMap_inj h)
  · intro p
    obtain ⟨v, hv⟩ := blochMap_surj p
    exact ⟨Quotient.mk _ v, hv⟩

/-- The bijection packaged as an equivalence: pure qubit states modulo global phase
are in bijection with the points of `S²`. -/
noncomputable def blochEquiv : PureState ≃ Sphere2 :=
  Equiv.ofBijective blochQuot bloch_sphere_bijection

end QC

#print axioms QC.bloch_sphere_bijection

