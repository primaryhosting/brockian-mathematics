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

-- (Lean requires `import` to precede any module docstring, so the header above is
-- repeated as the module docstring below.)
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

/-- A (normalised) pure qubit state vector: a unit vector `(a, b)` in `ℂ²`,
representing `a|0⟩ + b|1⟩`. -/
def Qubit : Type := {v : ℂ × ℂ // normSq v.1 + normSq v.2 = 1}

instance : CoeOut Qubit (ℂ × ℂ) := ⟨Subtype.val⟩

/-- Two unit vectors describe the same physical state when they differ by a global
phase `z` with `‖z‖ = 1`. -/
def phaseRel (v w : Qubit) : Prop :=
  ∃ z : ℂ, ‖z‖ = 1 ∧ (w : ℂ × ℂ).1 = z * (v : ℂ × ℂ).1 ∧ (w : ℂ × ℂ).2 = z * (v : ℂ × ℂ).2

lemma phaseRel_refl (v : Qubit) : phaseRel v v := ⟨1, by simp, by simp, by simp⟩

lemma phaseRel_symm {v w : Qubit} (h : phaseRel v w) : phaseRel w v := by
  obtain ⟨z, hz, h1, h2⟩ := h
  have hz0 : z ≠ 0 := by
    intro h; rw [h] at hz; simp at hz
  refine ⟨z⁻¹, by simp [hz], ?_, ?_⟩
  · rw [h1, ← mul_assoc, inv_mul_cancel₀ hz0, one_mul]
  · rw [h2, ← mul_assoc, inv_mul_cancel₀ hz0, one_mul]

lemma phaseRel_trans {u v w : Qubit} (h₁ : phaseRel u v) (h₂ : phaseRel v w) :
    phaseRel u w := by
  obtain ⟨z, hz, h1, h2⟩ := h₁
  obtain ⟨y, hy, g1, g2⟩ := h₂
  refine ⟨y * z, by simp [hy, hz], ?_, ?_⟩
  · rw [g1, h1, mul_assoc]
  · rw [g2, h2, mul_assoc]

/-- Physical equivalence of qubit state vectors: equality up to global phase. -/
instance phaseSetoid : Setoid Qubit where
  r := phaseRel
  iseqv := ⟨phaseRel_refl, phaseRel_symm, phaseRel_trans⟩

/-- Pure qubit states modulo global phase. -/
def QubitState : Type := Quotient phaseSetoid

/-- The 2-sphere `S² ⊆ ℝ³`. -/
abbrev S2 : Set (EuclideanSpace ℝ (Fin 3)) := Metric.sphere 0 1

lemma mem_S2_iff (x y z : ℝ) :
    (!₂[x, y, z] : EuclideanSpace ℝ (Fin 3)) ∈ S2 ↔ x ^ 2 + y ^ 2 + z ^ 2 = 1 := by
  rw [S2, mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq, Real.sqrt_eq_one]
  simp [Fin.sum_univ_three, sq_abs]

/-- The Bloch vector of a state vector `(a, b)`. -/
def blochVec (v : ℂ × ℂ) : EuclideanSpace ℝ (Fin 3) :=
  !₂[2 * ((starRingEnd ℂ) v.1 * v.2).re,
     2 * ((starRingEnd ℂ) v.1 * v.2).im,
     normSq v.1 - normSq v.2]

lemma blochVec_mem (v : Qubit) : blochVec (v : ℂ × ℂ) ∈ S2 := by
  obtain ⟨⟨a, b⟩, h⟩ := v
  simp only [blochVec]
  rw [mem_S2_iff]
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.conj_re,
    Complex.conj_im] at *
  ring_nf
  ring_nf at h
  nlinarith [h, sq_nonneg (a.re ^ 2 + a.im ^ 2 + b.re ^ 2 + b.im ^ 2)]

/-- The Bloch map on state vectors. -/
def blochRaw (v : Qubit) : S2 := ⟨blochVec (v : ℂ × ℂ), blochVec_mem v⟩

lemma blochRaw_wd {v w : Qubit} (h : phaseRel v w) : blochRaw v = blochRaw w := by
  obtain ⟨z, hz, h1, h2⟩ := h
  have hz1 : normSq z = 1 := Real.sqrt_eq_one.mp hz
  have key : (starRingEnd ℂ) (w : ℂ × ℂ).1 * (w : ℂ × ℂ).2
      = (starRingEnd ℂ) (v : ℂ × ℂ).1 * (v : ℂ × ℂ).2 := by
    rw [h1, h2, map_mul]
    have hc : (starRingEnd ℂ) z * z = (normSq z : ℂ) := normSq_eq_conj_mul_self.symm
    calc (starRingEnd ℂ) z * (starRingEnd ℂ) (v : ℂ × ℂ).1 * (z * (v : ℂ × ℂ).2)
        = ((starRingEnd ℂ) z * z) * ((starRingEnd ℂ) (v : ℂ × ℂ).1 * (v : ℂ × ℂ).2) := by ring
      _ = _ := by rw [hc, hz1]; simp
  have k1 : normSq (w : ℂ × ℂ).1 = normSq (v : ℂ × ℂ).1 := by rw [h1, map_mul, hz1, one_mul]
  have k2 : normSq (w : ℂ × ℂ).2 = normSq (v : ℂ × ℂ).2 := by rw [h2, map_mul, hz1, one_mul]
  apply Subtype.ext
  simp only [blochRaw, blochVec, key, k1, k2]

/-- The Bloch map: pure qubit states modulo global phase → `S²`. -/
def bloch : QubitState → S2 := Quotient.lift blochRaw (fun _ _ h => blochRaw_wd h)

/-- Two unit vectors with the same Bloch vector differ by a global phase. -/
lemma phaseRel_of_blochVec_eq {v w : Qubit}
    (h : blochVec (v : ℂ × ℂ) = blochVec (w : ℂ × ℂ)) : phaseRel v w := by
  obtain ⟨⟨a, b⟩, hv⟩ := v
  obtain ⟨⟨c, d⟩, hw⟩ := w
  simp only [blochVec] at h
  have e0 := congrFun (congrArg WithLp.ofLp h) 0
  have e1 := congrFun (congrArg WithLp.ofLp h) 1
  have e2 := congrFun (congrArg WithLp.ofLp h) 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons] at e0 e1 e2
  have habs : (starRingEnd ℂ) a * b = (starRingEnd ℂ) c * d :=
    Complex.ext (by linarith) (by linarith)
  have hn1 : normSq a = normSq c := by linarith
  have hn2 : normSq b = normSq d := by linarith
  by_cases ha : a = 0
  · have hc : c = 0 := by
      rw [← normSq_eq_zero, ← hn1, ha]; simp
    have hb : b ≠ 0 := by
      intro hb0
      rw [ha, hb0] at hv; simp at hv
    refine ⟨d / b, ?_, ?_, ?_⟩
    · have : ‖d‖ = ‖b‖ := by
        show Real.sqrt (normSq d) = Real.sqrt (normSq b)
        rw [hn2]
      rw [norm_div, this, div_self (by simpa using hb)]
    · show c = d / b * a
      rw [hc, ha, mul_zero]
    · show d = d / b * b
      field_simp
  · have hca : (starRingEnd ℂ) a ≠ 0 := by simpa using ha
    have hcb : c * b = a * d := by
      have hcc : c * (starRingEnd ℂ) c = (normSq c : ℂ) := mul_conj c
      have haa : a * (starRingEnd ℂ) a = (normSq a : ℂ) := mul_conj a
      have h1 : (starRingEnd ℂ) a * (c * b) = (starRingEnd ℂ) a * (a * d) := by
        calc (starRingEnd ℂ) a * (c * b) = c * ((starRingEnd ℂ) a * b) := by ring
          _ = c * ((starRingEnd ℂ) c * d) := by rw [habs]
          _ = (c * (starRingEnd ℂ) c) * d := by ring
          _ = (normSq c : ℂ) * d := by rw [hcc]
          _ = (normSq a : ℂ) * d := by rw [hn1]
          _ = (a * (starRingEnd ℂ) a) * d := by rw [haa]
          _ = (starRingEnd ℂ) a * (a * d) := by ring
      exact mul_left_cancel₀ hca h1
    refine ⟨c / a, ?_, ?_, ?_⟩
    · have hac : ‖c‖ = ‖a‖ := by
        show Real.sqrt (normSq c) = Real.sqrt (normSq a)
        rw [hn1]
      rw [norm_div, hac, div_self (by simpa using ha)]
    · show c = c / a * a
      field_simp
    · show d = c / a * b
      field_simp
      linear_combination -hcb

lemma bloch_injective : Function.Injective bloch := by
  intro q₁ q₂
  refine Quotient.inductionOn₂ q₁ q₂ ?_
  intro v w h
  exact Quotient.sound (phaseRel_of_blochVec_eq (congrArg Subtype.val h))

lemma bloch_surjective : Function.Surjective bloch := by
  rintro ⟨p, hp⟩
  set x := WithLp.ofLp p 0 with hx
  set y := WithLp.ofLp p 1 with hy
  set z := WithLp.ofLp p 2 with hz
  have hpe : p = !₂[x, y, z] := by
    ext i; fin_cases i <;> simp [hx, hy, hz]
  rw [hpe] at hp
  have hsum : x ^ 2 + y ^ 2 + z ^ 2 = 1 := (mem_S2_iff x y z).mp hp
  by_cases hz1 : z = -1
  · refine ⟨Quotient.mk _ ⟨(0, 1), by simp⟩, ?_⟩
    apply Subtype.ext
    have hx0 : x = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
    have hy0 : y = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
    show blochVec ((0 : ℂ), (1 : ℂ)) = p
    rw [hpe, hx0, hy0, hz1]
    simp only [blochVec]
    norm_num
  · have hzge : -1 < z := by
      rcases lt_trichotomy z (-1) with h | h | h
      · nlinarith [sq_nonneg x, sq_nonneg y]
      · exact absurd h hz1
      · exact h
    have hpos : (0:ℝ) < (1 + z) / 2 := by linarith
    set t := Real.sqrt ((1 + z) / 2) with htdef
    have ht0 : 0 < t := Real.sqrt_pos.mpr hpos
    have htne : t ≠ 0 := ne_of_gt ht0
    have ht2 : t ^ 2 = (1 + z) / 2 := Real.sq_sqrt (le_of_lt hpos)
    set a : ℂ := ⟨t, 0⟩ with hadef
    set b : ℂ := ⟨x / (2 * t), y / (2 * t)⟩ with hbdef
    have hnorm : normSq a + normSq b = 1 := by
      simp only [hadef, hbdef, Complex.normSq_mk]
      field_simp
      nlinarith [ht2, hsum]
    refine ⟨Quotient.mk _ ⟨(a, b), hnorm⟩, ?_⟩
    apply Subtype.ext
    show blochVec (a, b) = p
    rw [hpe]
    simp only [blochVec]
    have hA : 2 * ((starRingEnd ℂ) (a, b).1 * (a, b).2).re = x := by
      simp only [hadef, hbdef, Complex.mul_re, Complex.conj_re, Complex.conj_im]
      field_simp
      ring
    have hB : 2 * ((starRingEnd ℂ) (a, b).1 * (a, b).2).im = y := by
      simp only [hadef, hbdef, Complex.mul_im, Complex.conj_re, Complex.conj_im]
      field_simp
      ring
    have hC : normSq (a, b).1 - normSq (a, b).2 = z := by
      simp only [hadef, hbdef, Complex.normSq_mk]
      field_simp
      nlinarith [ht2, hsum]
    rw [hA, hB, hC]

/-- **Bloch sphere bijection.** Pure qubit states modulo global phase are in
bijection with the points of the 2-sphere `S² ⊆ ℝ³`, via the Bloch map
`a|0⟩ + b|1⟩ ↦ (2 Re(āb), 2 Im(āb), |a|² - |b|²)`. -/
theorem bloch_sphere_bijection : Function.Bijective bloch :=
  ⟨bloch_injective, bloch_surjective⟩

/-- Sanity check: the state `|0⟩` maps to the north pole of the Bloch sphere. -/
example : blochVec ((1 : ℂ), (0 : ℂ)) = !₂[0, 0, 1] := by
  simp [blochVec]

/-- Sanity check: the state `|1⟩` maps to the south pole of the Bloch sphere. -/
example : blochVec ((0 : ℂ), (1 : ℂ)) = !₂[0, 0, -1] := by
  simp [blochVec]

/-- The induced equivalence between pure qubit states modulo global phase and `S²`. -/
noncomputable def blochEquiv : QubitState ≃ S2 :=
  Equiv.ofBijective bloch bloch_sphere_bijection

/-- A remark: the abstract bijection `ℂP¹ ≃ S²` can also be assembled from existing Mathlib
results, namely `OnePoint.equivProjectivization : OnePoint K ≃ ℙ K (K × K)` and
`onePointEquivSphereOfFinrankEq : OnePoint V ≃ₜ sphere (0 : EuclideanSpace ℝ ι) 1`.
This yields a bijection between the complex projective line and `S²`, but not the explicit
Bloch map above (and it is phrased via projectivization of `ℂ²` rather than unit vectors
modulo phase). -/
noncomputable def projectivizationEquivSphere :
    Projectivization ℂ (ℂ × ℂ) ≃ S2 :=
  (OnePoint.equivProjectivization ℂ).symm.trans
    (onePointEquivSphereOfFinrankEq (V := ℂ) (ι := Fin 3) (by simp)).toEquiv

end QC

