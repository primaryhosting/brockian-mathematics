/-!
# Bloch Sphere Bijection
Category: Quantum Computing
Target: QC.bloch_sphere_bijection
Statement: Pure qubit states modulo global phase biject with points of the 2-sphere S².
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

open Complex ComplexConjugate

/-- A pure qubit state: a unit vector `(a, b)` in `ℂ²`. -/
structure Qubit where
  a : ℂ
  b : ℂ
  unit : normSq a + normSq b = 1

/-- Two pure qubit states are physically equal when they differ by a global phase. -/
def PhaseRel (q r : Qubit) : Prop :=
  ∃ c : ℂ, normSq c = 1 ∧ r.a = c * q.a ∧ r.b = c * q.b

instance phaseSetoid : Setoid Qubit where
  r := PhaseRel
  iseqv :=
    { refl := fun q => ⟨1, by simp, by simp, by simp⟩
      symm := by
        rintro q r ⟨c, hc, ha, hb⟩
        have hc0 : c ≠ 0 := by
          intro h; rw [h] at hc; simp at hc
        refine ⟨c⁻¹, ?_, ?_, ?_⟩
        · rw [Complex.normSq_inv, hc]; norm_num
        · rw [ha]; field_simp
        · rw [hb]; field_simp
      trans := by
        rintro q r s ⟨c, hc, ha, hb⟩ ⟨d, hd, ha', hb'⟩
        exact ⟨d * c, by rw [Complex.normSq_mul, hc, hd]; ring,
          by rw [ha', ha]; ring, by rw [hb', hb]; ring⟩ }

/-- Pure qubit states modulo global phase. -/
def PureState : Type := Quotient phaseSetoid

/-- The 2-sphere `S² ⊆ ℝ³`, described in coordinates. -/
def Sphere2 : Type := {p : ℝ × ℝ × ℝ // p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 = 1}

/-- The Bloch vector of a pure qubit state. -/
def blochVec (q : Qubit) : ℝ × ℝ × ℝ :=
  (2 * (q.a * conj q.b).re, 2 * (q.a * conj q.b).im, normSq q.a - normSq q.b)

lemma normSq_mul_conj_eq (z w : ℂ) :
    (z * conj w).re ^ 2 + (z * conj w).im ^ 2 = normSq z * normSq w := by
  have h : normSq (z * conj w) = normSq z * normSq w := by
    rw [Complex.normSq_mul, Complex.normSq_conj]
  rw [Complex.normSq_apply] at h
  nlinarith [h]

lemma blochVec_mem (q : Qubit) :
    (blochVec q).1 ^ 2 + (blochVec q).2.1 ^ 2 + (blochVec q).2.2 ^ 2 = 1 := by
  have h := normSq_mul_conj_eq q.a q.b
  have hu := q.unit
  simp only [blochVec]
  nlinarith [h, hu]

/-- The Bloch map on pure qubit states. -/
def blochQ (q : Qubit) : Sphere2 := ⟨blochVec q, blochVec_mem q⟩

lemma blochQ_of_phase {q r : Qubit} (h : PhaseRel q r) : blochQ q = blochQ r := by
  obtain ⟨c, hc, ha, hb⟩ := h
  have hmul : r.a * conj r.b = q.a * conj q.b := by
    rw [ha, hb, map_mul]
    have hcc : c * conj c = (normSq c : ℂ) := by rw [Complex.mul_conj]
    calc c * q.a * (conj c * conj q.b) = (c * conj c) * (q.a * conj q.b) := by ring
      _ = q.a * conj q.b := by rw [hcc, hc]; simp
  have hna : normSq r.a = normSq q.a := by rw [ha, Complex.normSq_mul, hc, one_mul]
  have hnb : normSq r.b = normSq q.b := by rw [hb, Complex.normSq_mul, hc, one_mul]
  apply Subtype.ext
  simp only [blochQ, blochVec, hmul, hna, hnb]

/-- The Bloch map, descended to pure states modulo global phase. -/
def bloch : PureState → Sphere2 :=
  Quotient.lift blochQ (fun _ _ h => blochQ_of_phase h)

lemma bloch_mk (q : Qubit) : bloch (Quotient.mk phaseSetoid q) = blochQ q := rfl

/-- Two pure qubit states with the same Bloch vector differ by a global phase. -/
lemma blochQ_inj {q r : Qubit} (h : blochQ q = blochQ r) : PhaseRel q r := by
  have h' := congrArg Subtype.val h
  simp only [blochQ, blochVec, Prod.ext_iff] at h'
  have h1 : q.a * conj q.b = r.a * conj r.b := by
    apply Complex.ext <;> linarith [h'.1, h'.2.1]
  have h2 : normSq q.a - normSq q.b = normSq r.a - normSq r.b := h'.2.2
  have hqa : normSq q.a = normSq r.a := by linarith [q.unit, r.unit, h2]
  have hqb : normSq q.b = normSq r.b := by linarith [q.unit, r.unit, h2]
  by_cases hz : q.a = 0
  · have hra : r.a = 0 := by
      have hz' : normSq r.a = 0 := by rw [← hqa, hz]; simp
      exact Complex.normSq_eq_zero.mp hz'
    have hb0 : q.b ≠ 0 := by
      intro hb
      have hu := q.unit
      rw [hz, hb] at hu
      simp at hu
    refine ⟨r.b / q.b, ?_, ?_, ?_⟩
    · rw [Complex.normSq_div, hqb]
      have hnz : normSq r.b ≠ 0 := by rw [← hqb]; simpa using hb0
      field_simp
    · rw [hra, hz]; ring
    · field_simp
  · refine ⟨r.a / q.a, ?_, ?_, ?_⟩
    · rw [Complex.normSq_div, hqa]
      have hnz : normSq r.a ≠ 0 := by rw [← hqa]; simpa using hz
      field_simp
    · field_simp
    · have key : r.a * q.b = q.a * r.b := by
        have hc : conj q.a * q.b = conj r.a * r.b := by
          have hcg := congrArg (starRingEnd ℂ) h1
          simpa [map_mul, mul_comm] using hcg
        have e2 : r.a * conj r.a = (normSq r.a : ℂ) := by rw [Complex.mul_conj]
        have e3 : q.a * conj q.a = (normSq q.a : ℂ) := by rw [Complex.mul_conj]
        have hqa' : ((normSq q.a : ℝ) : ℂ) = ((normSq r.a : ℝ) : ℂ) := by rw [hqa]
        have hane : conj q.a ≠ 0 := by simpa using hz
        have hcancel : conj q.a * (r.a * q.b) = conj q.a * (q.a * r.b) := by
          calc conj q.a * (r.a * q.b) = r.a * (conj q.a * q.b) := by ring
            _ = r.a * (conj r.a * r.b) := by rw [hc]
            _ = (r.a * conj r.a) * r.b := by ring
            _ = ((normSq r.a : ℝ) : ℂ) * r.b := by rw [e2]
            _ = ((normSq q.a : ℝ) : ℂ) * r.b := by rw [hqa']
            _ = (q.a * conj q.a) * r.b := by rw [e3]
            _ = conj q.a * (q.a * r.b) := by ring
        exact mul_left_cancel₀ hane hcancel
      field_simp
      linear_combination -key

/-- Every point of the 2-sphere is the Bloch vector of some pure qubit state. -/
lemma blochQ_surj (p : Sphere2) : ∃ q : Qubit, blochQ q = p := by
  obtain ⟨⟨x, y, z⟩, hp⟩ := p
  simp only at hp
  by_cases hz : z = -1
  · refine ⟨⟨0, 1, by simp⟩, ?_⟩
    have hx : x = 0 ∧ y = 0 := by
      constructor <;> nlinarith [sq_nonneg x, sq_nonneg y]
    apply Subtype.ext
    simp [blochQ, blochVec, hx.1, hx.2, hz]
  · have hz1 : (0:ℝ) < 1 + z := by
      rcases lt_trichotomy (1 + z) 0 with h | h | h
      · nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg (1 + z)]
      · exact absurd (by linarith : z = -1) hz
      · exact h
    set t : ℝ := Real.sqrt ((1 + z) / 2) with ht
    have ht2 : t ^ 2 = (1 + z) / 2 := Real.sq_sqrt (by linarith)
    have htpos : 0 < t := Real.sqrt_pos.mpr (by linarith)
    have hne : t ≠ 0 := ne_of_gt htpos
    set u : ℝ := x / (2 * t) with hu
    set v : ℝ := -(y / (2 * t)) with hv
    have huv : u ^ 2 + v ^ 2 = (1 - z) / 2 := by
      rw [hu, hv]
      field_simp
      nlinarith [ht2, hp]
    have hnb : normSq ((u : ℂ) + (v : ℂ) * I) = u ^ 2 + v ^ 2 := by
      simp [Complex.normSq_apply]; ring
    have hna : normSq ((t : ℝ) : ℂ) = t ^ 2 := by
      simp [Complex.normSq_apply]; ring
    refine ⟨⟨(t : ℂ), (u : ℂ) + (v : ℂ) * I, ?_⟩, ?_⟩
    · rw [hna, hnb, huv, ht2]; ring
    · apply Subtype.ext
      have hre : ((t : ℂ) * conj ((u : ℂ) + (v : ℂ) * I)).re = t * u := by
        simp [Complex.mul_re]
      have him : ((t : ℂ) * conj ((u : ℂ) + (v : ℂ) * I)).im = -(t * v) := by
        simp [Complex.mul_im]
      simp only [blochQ, blochVec, Prod.mk.injEq, hre, him, hna, hnb, huv, ht2]
      refine ⟨?_, ?_, by ring⟩
      · rw [hu]; field_simp
      · rw [hv]; field_simp

/-- **The Bloch sphere.**  Pure qubit states modulo global phase are in bijection with the
points of the 2-sphere `S²`. -/
theorem bloch_sphere_bijection : Function.Bijective bloch := by
  constructor
  · intro u v h
    induction u using Quotient.inductionOn with
    | _ q =>
      induction v using Quotient.inductionOn with
      | _ r =>
        exact Quotient.sound (blochQ_inj h)
  · rintro p
    obtain ⟨q, hq⟩ := blochQ_surj p
    exact ⟨Quotient.mk phaseSetoid q, hq⟩

/-- The Bloch bijection, packaged as an equivalence. -/
noncomputable def blochEquiv : PureState ≃ Sphere2 :=
  Equiv.ofBijective bloch bloch_sphere_bijection

/-! ### Identification of `Sphere2` with the unit sphere of `ℝ³` -/

lemma euclidean_norm_three_eq_one_iff (v : EuclideanSpace ℝ (Fin 3)) :
    ‖v‖ = 1 ↔ v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1 := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one, Fin.sum_univ_three]
  simp [sq_abs]

/-- The coordinate description `Sphere2` really is the unit sphere `S²` of `ℝ³`. -/
noncomputable def sphere2Equiv : Sphere2 ≃ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 where
  toFun p :=
    ⟨(EuclideanSpace.equiv (Fin 3) ℝ).symm ![p.1.1, p.1.2.1, p.1.2.2], by
      rw [mem_sphere_zero_iff_norm, euclidean_norm_three_eq_one_iff]
      simpa using p.2⟩
  invFun w :=
    ⟨(w.1 0, w.1 1, w.1 2), by
      have := mem_sphere_zero_iff_norm.mp w.2
      exact (euclidean_norm_three_eq_one_iff _).mp this⟩
  left_inv p := by
    apply Subtype.ext
    simp
  right_inv w := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp

/-- Pure qubit states modulo global phase are in bijection with the unit sphere of `ℝ³`. -/
noncomputable def blochEquivSphere :
    PureState ≃ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  blochEquiv.trans sphere2Equiv

end QC


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

