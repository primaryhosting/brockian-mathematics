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

open Complex

/-- A normalized qubit state vector: a unit vector in `ℂ²`. -/
def Qubit : Type := {v : ℂ × ℂ // normSq v.1 + normSq v.2 = 1}

/-- Two state vectors are identified when they differ by a global phase. -/
instance phaseSetoid : Setoid Qubit where
  r v w := ∃ c : ℂ, normSq c = 1 ∧ w.val = (c * v.val.1, c * v.val.2)
  iseqv := by
    constructor
    · intro v
      exact ⟨1, by simp, by simp⟩
    · rintro v w ⟨c, hc, hw⟩
      have hc0 : c ≠ 0 := by
        intro h; rw [h] at hc; simp at hc
      refine ⟨c⁻¹, ?_, ?_⟩
      · rw [Complex.normSq_inv, hc]; norm_num
      · simp only [hw]
        rw [Prod.ext_iff]
        exact ⟨by field_simp, by field_simp⟩
    · rintro u v w ⟨c, hc, hv⟩ ⟨d, hd, hw⟩
      refine ⟨d * c, by rw [Complex.normSq_mul, hc, hd]; norm_num, ?_⟩
      rw [hw, hv]
      simp only [Prod.mk.injEq]
      constructor <;> ring

/-- Pure qubit states: unit vectors in `ℂ²` modulo global phase. -/
def PureState : Type := Quotient phaseSetoid

/-- The 2-sphere `S²` inside `ℝ³`. -/
def S2 : Set (EuclideanSpace ℝ (Fin 3)) := Metric.sphere 0 1

lemma mem_S2_iff (x : EuclideanSpace ℝ (Fin 3)) :
    x ∈ S2 ↔ x.ofLp 0 ^ 2 + x.ofLp 1 ^ 2 + x.ofLp 2 ^ 2 = 1 := by
  rw [S2, mem_sphere_iff_norm, sub_zero, EuclideanSpace.norm_eq]
  constructor
  · intro h
    have h2 := Real.sq_sqrt (by positivity : (0:ℝ) ≤ ∑ i, ‖x.ofLp i‖ ^ 2)
    rw [h] at h2
    simpa [Fin.sum_univ_three, sq_abs] using h2.symm
  · intro h
    rw [show (∑ i, ‖x.ofLp i‖ ^ 2) = 1 by simpa [Fin.sum_univ_three, sq_abs] using h]
    simp

/-- The Bloch vector of a state vector `(a, b) ∈ ℂ²`. -/
noncomputable def blochVec (v : ℂ × ℂ) : EuclideanSpace ℝ (Fin 3) :=
  !₂[2 * ((starRingEnd ℂ) v.1 * v.2).re, 2 * ((starRingEnd ℂ) v.1 * v.2).im,
     normSq v.1 - normSq v.2]

@[simp] lemma blochVec_zero (v : ℂ × ℂ) :
    (blochVec v).ofLp 0 = 2 * ((starRingEnd ℂ) v.1 * v.2).re := rfl

@[simp] lemma blochVec_one (v : ℂ × ℂ) :
    (blochVec v).ofLp 1 = 2 * ((starRingEnd ℂ) v.1 * v.2).im := rfl

@[simp] lemma blochVec_two (v : ℂ × ℂ) :
    (blochVec v).ofLp 2 = normSq v.1 - normSq v.2 := rfl

lemma blochVec_mem_S2 (v : Qubit) : blochVec v.val ∈ S2 := by
  obtain ⟨⟨a, b⟩, h⟩ := v
  rw [mem_S2_iff]
  simp only [blochVec_zero, blochVec_one, blochVec_two]
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.conj_re,
    Complex.conj_im] at *
  linear_combination (a.re * a.re + a.im * a.im + b.re * b.re + b.im * b.im + 1) * h

/-- The Bloch vector is invariant under a global phase. -/
lemma blochVec_phase (a b c : ℂ) (hc : normSq c = 1) : blochVec (c * a, c * b) = blochVec (a, b) := by
  simp only [blochVec, map_mul]
  congr 1
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.conj_re,
    Complex.conj_im] at *
  ext i
  fin_cases i <;> simp <;>
    first
      | linear_combination (a.re * b.re + a.im * b.im) * hc
      | linear_combination (a.re * b.im - a.im * b.re) * hc
      | linear_combination (a.re * a.re + a.im * a.im - b.re * b.re - b.im * b.im) * hc

/-- The Bloch vector of a normalized qubit state, as a point of `S²`. -/
noncomputable def blochQubit (v : Qubit) : S2 := ⟨blochVec v.val, blochVec_mem_S2 v⟩

lemma blochQubit_phase_invariant (v w : Qubit) (h : v ≈ w) : blochQubit v = blochQubit w := by
  obtain ⟨c, hc, hw⟩ := h
  apply Subtype.ext
  show blochVec v.val = blochVec w.val
  rw [show w.val = (c * v.val.1, c * v.val.2) from hw, blochVec_phase _ _ _ hc]

/-- The Bloch map: pure qubit states (unit vectors mod global phase) to points of `S²`. -/
noncomputable def bloch : PureState → S2 :=
  Quotient.lift blochQubit blochQubit_phase_invariant

lemma bloch_mk (v : Qubit) : bloch (Quotient.mk phaseSetoid v) = blochQubit v := rfl

/-- Two unit vectors of `ℂ²` with the same first-coordinate modulus and the same
inner product `⟪a, b⟫` differ by a global phase. -/
lemma phase_of_data (a b a' b' : ℂ) (hv : normSq a + normSq b = 1) (hv' : normSq a' + normSq b' = 1)
    (hna : normSq a = normSq a') (hcj : (starRingEnd ℂ) a * b = (starRingEnd ℂ) a' * b') :
    ∃ c : ℂ, normSq c = 1 ∧ (a', b') = (c * a, c * b) := by
  by_cases ha : a = 0
  · have ha' : a' = 0 := by
      have h0 : normSq a' = 0 := by rw [← hna, ha]; simp
      exact Complex.normSq_eq_zero.mp h0
    have hb : normSq b = 1 := by rw [ha] at hv; simpa using hv
    have hb' : normSq b' = 1 := by rw [ha'] at hv'; simpa using hv'
    have hb0 : b ≠ 0 := fun h => by simp [h] at hb
    refine ⟨b' / b, ?_, ?_⟩
    · rw [Complex.normSq_div, hb, hb']; norm_num
    · simp only [Prod.mk.injEq]
      exact ⟨by rw [ha, ha']; ring, by field_simp⟩
  · have ha0 : normSq a ≠ 0 := fun h => ha (Complex.normSq_eq_zero.mp h)
    have ha0' : normSq a' ≠ 0 := by rw [← hna]; exact ha0
    refine ⟨a' / a, ?_, ?_⟩
    · rw [Complex.normSq_div, hna]
      field_simp
    · simp only [Prod.mk.injEq]
      refine ⟨by field_simp, ?_⟩
      have key : a' * b * (starRingEnd ℂ) a = normSq a' * b' := by
        rw [show a' * b * (starRingEnd ℂ) a = a' * ((starRingEnd ℂ) a * b) by ring, hcj,
          show a' * ((starRingEnd ℂ) a' * b') = (a' * (starRingEnd ℂ) a') * b' by ring,
          Complex.mul_conj]
      have hmc : a * (starRingEnd ℂ) a = normSq a := Complex.mul_conj a
      have hca : (starRingEnd ℂ) a ≠ 0 := by simpa using ha
      have hkey : a' * b = b' * a := by
        refine mul_right_cancel₀ hca ?_
        rw [key, show b' * a * (starRingEnd ℂ) a = (a * (starRingEnd ℂ) a) * b' by ring, hmc, hna]
      field_simp
      linear_combination -hkey

lemma bloch_injective_aux (v w : Qubit) (h : blochVec v.val = blochVec w.val) : v ≈ w := by
  obtain ⟨⟨a, b⟩, hv⟩ := v
  obtain ⟨⟨a', b'⟩, hv'⟩ := w
  simp only at h hv hv' ⊢
  have h0 : 2 * ((starRingEnd ℂ) a * b).re = 2 * ((starRingEnd ℂ) a' * b').re :=
    congrArg (fun t : EuclideanSpace ℝ (Fin 3) => t.ofLp 0) h
  have h1 : 2 * ((starRingEnd ℂ) a * b).im = 2 * ((starRingEnd ℂ) a' * b').im :=
    congrArg (fun t : EuclideanSpace ℝ (Fin 3) => t.ofLp 1) h
  have h2 : normSq a - normSq b = normSq a' - normSq b' :=
    congrArg (fun t : EuclideanSpace ℝ (Fin 3) => t.ofLp 2) h
  have hna : normSq a = normSq a' := by linarith
  have hcj : (starRingEnd ℂ) a * b = (starRingEnd ℂ) a' * b' :=
    Complex.ext (by linarith) (by linarith)
  exact phase_of_data a b a' b' hv hv' hna hcj

lemma bloch_surjective_aux (p : S2) : ∃ v : Qubit, blochQubit v = p := by
  obtain ⟨p, hp⟩ := p
  rw [mem_S2_iff] at hp
  obtain ⟨x, y, z, hx, hy, hz⟩ :
      ∃ x y z : ℝ, p.ofLp 0 = x ∧ p.ofLp 1 = y ∧ p.ofLp 2 = z := ⟨_, _, _, rfl, rfl, rfl⟩
  rw [hx, hy, hz] at hp
  have main : ∃ a b : ℂ, normSq a + normSq b = 1 ∧ 2 * ((starRingEnd ℂ) a * b).re = x ∧
      2 * ((starRingEnd ℂ) a * b).im = y ∧ normSq a - normSq b = z := by
    by_cases hzz : z = -1
    · have hx0 : x = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
      have hy0 : y = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
      exact ⟨0, 1, by simp, by simp [hx0], by simp [hy0], by simp [hzz]⟩
    · have hz1 : -1 ≤ z := by
        nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg (z + 1), sq_nonneg (z - 1)]
      have hzpos : 0 < 1 + z := lt_of_le_of_ne (by linarith) (fun hh => hzz (by linarith))
      obtain ⟨r, hr, hr2⟩ : ∃ r : ℝ, 0 < r ∧ r ^ 2 = (1 + z) / 2 :=
        ⟨Real.sqrt ((1 + z) / 2), Real.sqrt_pos.mpr (by linarith), Real.sq_sqrt (by linarith)⟩
      obtain ⟨s, hs⟩ : ∃ s : ℝ, s = x / (2 * r) := ⟨_, rfl⟩
      obtain ⟨t, ht⟩ : ∃ t : ℝ, t = y / (2 * r) := ⟨_, rfl⟩
      have h2r : (2 * r) ≠ 0 := by positivity
      have hsx : 2 * r * s = x := by rw [hs]; field_simp
      have hty : 2 * r * t = y := by rw [ht]; field_simp
      have h' : (2 * r * s) ^ 2 + (2 * r * t) ^ 2 + z ^ 2 = 1 := by rw [hsx, hty]; exact hp
      have hst : s ^ 2 + t ^ 2 = (1 - z) / 2 := by
        refine mul_left_cancel₀ (ne_of_gt hzpos) ?_
        linear_combination (1 / 2) * h' - 2 * (s ^ 2 + t ^ 2) * hr2
      refine ⟨(r : ℂ), (s : ℂ) + (t : ℂ) * Complex.I, ?_, ?_, ?_, ?_⟩
      · simp only [Complex.normSq_apply, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
          Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
        ring_nf
        linarith [hr2, hst]
      · simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.I_re,
          Complex.I_im]
        linarith [hsx]
      · simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.I_re,
          Complex.I_im]
        linarith [hty]
      · simp only [Complex.normSq_apply, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
          Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
        ring_nf
        linarith [hr2, hst]
  obtain ⟨a, b, hab, hbx, hby, hbz⟩ := main
  refine ⟨⟨(a, b), hab⟩, ?_⟩
  apply Subtype.ext
  show blochVec (a, b) = p
  have hbx' : 2 * (a.re * b.re + a.im * b.im) = x := by
    rw [← hbx, Complex.mul_re, Complex.conj_re, Complex.conj_im]; ring
  have hby' : 2 * (a.re * b.im + -(a.im * b.re)) = y := by
    rw [← hby, Complex.mul_im, Complex.conj_re, Complex.conj_im]; ring
  ext i
  fin_cases i <;> simp [blochVec, hbz, hx, hy, hz] <;> linarith [hbx', hby']

/-- **Bloch sphere bijection**: pure qubit states (unit vectors in `ℂ²` modulo global
phase) are in bijection with the points of the 2-sphere `S² ⊆ ℝ³`, via the Bloch map. -/
theorem bloch_sphere_bijection : Function.Bijective bloch := by
  constructor
  · intro X Y hXY
    induction X using Quotient.inductionOn with
    | h v =>
      induction Y using Quotient.inductionOn with
      | h w =>
        refine Quotient.sound (bloch_injective_aux v w ?_)
        have := congrArg Subtype.val hXY
        simpa [bloch_mk, blochQubit] using this
  · intro p
    obtain ⟨v, hv⟩ := bloch_surjective_aux p
    exact ⟨Quotient.mk phaseSetoid v, hv⟩

end QC

