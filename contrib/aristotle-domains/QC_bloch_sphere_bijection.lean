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

lemma mem_sphere_two_iff (v : EuclideanSpace ℂ (Fin 2)) :
    v ∈ Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1 ↔
      Complex.normSq (v 0) + Complex.normSq (v 1) = 1 := by
  rw [mem_sphere_iff_norm, sub_zero, EuclideanSpace.norm_eq, Fin.sum_univ_two,
    Real.sqrt_eq_one]
  simp [Complex.normSq_eq_norm_sq]

lemma mem_sphere_three_iff (p : EuclideanSpace ℝ (Fin 3)) :
    p ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↔
      p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 = 1 := by
  rw [mem_sphere_iff_norm, sub_zero, EuclideanSpace.norm_eq, Fin.sum_univ_three,
    Real.sqrt_eq_one]
  simp [sq_abs]

/-- Two pure states are physically equal when they differ by a global phase. -/
def PhaseRel (v w : PureQubit) : Prop :=
  ∃ z : ℂ, ‖z‖ = 1 ∧ (w : EuclideanSpace ℂ (Fin 2)) = z • (v : EuclideanSpace ℂ (Fin 2))

instance phaseSetoid : Setoid PureQubit where
  r := PhaseRel
  iseqv := by
    constructor
    · intro v
      exact ⟨1, by simp, by simp⟩
    · rintro v w ⟨z, hz, hvw⟩
      refine ⟨z⁻¹, by simp [hz], ?_⟩
      have hz0 : z ≠ 0 := by
        intro h; rw [h] at hz; simp at hz
      rw [hvw, smul_smul, inv_mul_cancel₀ hz0, one_smul]
    · rintro u v w ⟨z, hz, huv⟩ ⟨y, hy, hvw⟩
      exact ⟨y * z, by simp [hy, hz], by rw [hvw, huv, smul_smul]⟩

/-- Pure qubit states modulo global phase. -/
def PureQubitModPhase : Type := Quotient phaseSetoid

/-- The Bloch vector of a vector in `ℂ²`. -/
noncomputable def blochVec (v : EuclideanSpace ℂ (Fin 2)) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![2 * ((starRingEnd ℂ) (v 0) * v 1).re,
    2 * ((starRingEnd ℂ) (v 0) * v 1).im,
    Complex.normSq (v 0) - Complex.normSq (v 1)]

@[simp] lemma blochVec_zero (v : EuclideanSpace ℂ (Fin 2)) :
    blochVec v 0 = 2 * ((starRingEnd ℂ) (v 0) * v 1).re := rfl

@[simp] lemma blochVec_one (v : EuclideanSpace ℂ (Fin 2)) :
    blochVec v 1 = 2 * ((starRingEnd ℂ) (v 0) * v 1).im := rfl

@[simp] lemma blochVec_two (v : EuclideanSpace ℂ (Fin 2)) :
    blochVec v 2 = Complex.normSq (v 0) - Complex.normSq (v 1) := rfl

lemma blochVec_mem (v : PureQubit) :
    blochVec (v : EuclideanSpace ℂ (Fin 2)) ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  have hv : Complex.normSq ((v : EuclideanSpace ℂ (Fin 2)) 0)
      + Complex.normSq ((v : EuclideanSpace ℂ (Fin 2)) 1) = 1 :=
    (mem_sphere_two_iff _).1 v.2
  rw [mem_sphere_three_iff]
  simp only [blochVec_zero, blochVec_one, blochVec_two]
  set a := (v : EuclideanSpace ℂ (Fin 2)) 0
  set b := (v : EuclideanSpace ℂ (Fin 2)) 1
  have h : (2 * ((starRingEnd ℂ) a * b).re) ^ 2 + (2 * ((starRingEnd ℂ) a * b).im) ^ 2
      + (Complex.normSq a - Complex.normSq b) ^ 2
      = (Complex.normSq a + Complex.normSq b) ^ 2 := by
    simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    ring
  rw [h, hv, one_pow]

lemma blochVec_smul (z : ℂ) (hz : ‖z‖ = 1) (v : EuclideanSpace ℂ (Fin 2)) :
    blochVec (z • v) = blochVec v := by
  have hz' : Complex.normSq z = 1 := by
    rw [Complex.normSq_eq_norm_sq, hz, one_pow]
  have h0 : (z • v) 0 = z * v 0 := rfl
  have h1 : (z • v) 1 = z * v 1 := rfl
  have key : (starRingEnd ℂ) ((z • v) 0) * (z • v) 1 = (starRingEnd ℂ) (v 0) * v 1 := by
    rw [h0, h1, map_mul]
    have : (starRingEnd ℂ) z * z = (Complex.normSq z : ℂ) := by
      rw [Complex.normSq_eq_conj_mul_self]
    calc (starRingEnd ℂ) z * (starRingEnd ℂ) (v 0) * (z * v 1)
        = ((starRingEnd ℂ) z * z) * ((starRingEnd ℂ) (v 0) * v 1) := by ring
      _ = (starRingEnd ℂ) (v 0) * v 1 := by rw [this, hz']; simp
  unfold blochVec
  rw [key, h0, h1, Complex.normSq_mul, Complex.normSq_mul, hz']
  ring_nf

/-- The Bloch map from pure states modulo phase to the 2-sphere. -/
noncomputable def blochMap : PureQubitModPhase → S2 :=
  Quotient.lift (fun v : PureQubit => (⟨blochVec (v : EuclideanSpace ℂ (Fin 2)),
      blochVec_mem v⟩ : S2))
    (by
      rintro v w ⟨z, hz, hvw⟩
      apply Subtype.ext
      simp only
      rw [hvw, blochVec_smul z hz])

@[simp] lemma blochMap_mk (v : PureQubit) :
    (blochMap (Quotient.mk phaseSetoid v) : EuclideanSpace ℝ (Fin 3))
      = blochVec (v : EuclideanSpace ℂ (Fin 2)) := rfl

lemma norm_eq_one_of_normSq_eq_one {z : ℂ} (h : Complex.normSq z = 1) : ‖z‖ = 1 := by
  have h2 : ‖z‖ ^ 2 = 1 := by rw [← Complex.normSq_eq_norm_sq, h]
  nlinarith [norm_nonneg z]

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


lemma S2_ext (u p : EuclideanSpace ℝ (Fin 3)) (h0 : u 0 = p 0) (h1 : u 1 = p 1)
    (h2 : u 2 = p 2) : u = p := by
  refine PiLp.ext (fun i => ?_)
  fin_cases i
  exacts [h0, h1, h2]

lemma blochMap_surjective : Function.Surjective blochMap := by
  rintro ⟨p, hp⟩
  have hsum : p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 = 1 := (mem_sphere_three_iff p).1 hp
  by_cases hz : p 2 = -1
  · have hx : p 0 = 0 := by nlinarith [sq_nonneg (p 0), sq_nonneg (p 1)]
    have hy : p 1 = 0 := by nlinarith [sq_nonneg (p 0), sq_nonneg (p 1)]
    have hmem : (WithLp.toLp 2 ![(0 : ℂ), 1] : EuclideanSpace ℂ (Fin 2))
        ∈ Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1 := by
      rw [mem_sphere_two_iff]
      show Complex.normSq (0 : ℂ) + Complex.normSq (1 : ℂ) = 1
      simp
    refine ⟨Quotient.mk phaseSetoid ⟨_, hmem⟩, ?_⟩
    apply Subtype.ext
    rw [blochMap_mk]
    refine S2_ext _ _ ?_ ?_ ?_
    · show 2 * ((starRingEnd ℂ) (0 : ℂ) * (1 : ℂ)).re = p 0
      simp [hx]
    · show 2 * ((starRingEnd ℂ) (0 : ℂ) * (1 : ℂ)).im = p 1
      simp [hy]
    · show Complex.normSq (0 : ℂ) - Complex.normSq (1 : ℂ) = p 2
      simp [hz]
  · have hge : -1 ≤ p 2 := by nlinarith [sq_nonneg (p 0), sq_nonneg (p 1), sq_nonneg (p 2 + 1)]
    have hgt : -1 < p 2 := lt_of_le_of_ne hge (Ne.symm hz)
    set r := Real.sqrt ((1 + p 2) / 2) with hrdef
    have hrpos : 0 < r := Real.sqrt_pos.2 (by linarith)
    have hr2 : r ^ 2 = (1 + p 2) / 2 := Real.sq_sqrt (by linarith)
    set bb : ℂ := ⟨p 0 / (2 * r), p 1 / (2 * r)⟩ with hbb
    have hbbre : bb.re = p 0 / (2 * r) := rfl
    have hbbim : bb.im = p 1 / (2 * r) := rfl
    have hnb : Complex.normSq bb = (1 - p 2) / 2 := by
      rw [Complex.normSq_apply, hbbre, hbbim]
      field_simp
      nlinarith [hr2, hsum]
    have hna : Complex.normSq ((r : ℝ) : ℂ) = (1 + p 2) / 2 := by
      rw [Complex.normSq_ofReal]
      nlinarith [hr2]
    have hmem : (WithLp.toLp 2 ![((r : ℝ) : ℂ), bb] : EuclideanSpace ℂ (Fin 2))
        ∈ Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1 := by
      rw [mem_sphere_two_iff]
      show Complex.normSq ((r : ℝ) : ℂ) + Complex.normSq bb = 1
      rw [hna, hnb]; ring
    refine ⟨Quotient.mk phaseSetoid ⟨_, hmem⟩, ?_⟩
    apply Subtype.ext
    rw [blochMap_mk]
    refine S2_ext _ _ ?_ ?_ ?_
    · show 2 * ((starRingEnd ℂ) ((r : ℝ) : ℂ) * bb).re = p 0
      rw [Complex.mul_re, Complex.conj_ofReal, Complex.ofReal_re, Complex.ofReal_im, hbbre]
      field_simp
      ring
    · show 2 * ((starRingEnd ℂ) ((r : ℝ) : ℂ) * bb).im = p 1
      rw [Complex.mul_im, Complex.conj_ofReal, Complex.ofReal_re, Complex.ofReal_im, hbbim]
      field_simp
      ring
    · show Complex.normSq ((r : ℝ) : ℂ) - Complex.normSq bb = p 2
      rw [hna, hnb]; ring


/-- **Bloch sphere correspondence**: pure qubit states modulo global phase are in
bijection with the points of the 2-sphere `S²`, via the Bloch map. -/
theorem bloch_sphere_bijection : Function.Bijective blochMap :=
  ⟨blochMap_injective, blochMap_surjective⟩

/-- The induced equivalence between pure qubit states modulo global phase and `S²`. -/
noncomputable def blochEquiv : PureQubitModPhase ≃ S2 :=
  Equiv.ofBijective blochMap bloch_sphere_bijection

end QC

