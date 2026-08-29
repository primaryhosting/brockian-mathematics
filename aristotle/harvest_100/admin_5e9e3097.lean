/-
# Bloch Sphere Bijection
Category: Quantum Computing
Target: QC.bloch_sphere_bijection
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is written as a plain block comment rather than a module
-- docstring `/-! ... -/` because Lean 4 requires all `import` commands to come
-- before any command, and a module docstring counts as a command.)
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

/-- A (normalized) pure qubit state vector: a unit vector of `ℂ²`. -/
def QubitState : Type := {p : ℂ × ℂ // normSq p.1 + normSq p.2 = 1}

/-- Two unit vectors of `ℂ²` describe the same physical state iff they differ by
a global phase `u` with `|u| = 1`. -/
def PhaseRel (p q : QubitState) : Prop :=
  ∃ u : ℂ, normSq u = 1 ∧ q.1.1 = u * p.1.1 ∧ q.1.2 = u * p.1.2

theorem phaseRel_equivalence : Equivalence PhaseRel := by
  constructor
  · intro p
    exact ⟨1, by simp, by simp, by simp⟩
  · rintro p q ⟨u, hu, h1, h2⟩
    have hu0 : u ≠ 0 := by
      intro h; rw [h] at hu; simp at hu
    refine ⟨u⁻¹, ?_, ?_, ?_⟩
    · rw [map_inv₀, hu]; simp
    · rw [h1]; field_simp
    · rw [h2]; field_simp
  · rintro p q r ⟨u, hu, h1, h2⟩ ⟨v, hv, k1, k2⟩
    refine ⟨v * u, ?_, ?_, ?_⟩
    · rw [map_mul, hu, hv]; ring
    · rw [k1, h1]; ring
    · rw [k2, h2]; ring

instance phaseSetoid : Setoid QubitState := ⟨PhaseRel, phaseRel_equivalence⟩

/-- The space of pure qubit states modulo global phase (i.e. `ℂP¹`). -/
def PureQubit : Type := Quotient phaseSetoid

/-- The 2-sphere `S² ⊆ ℝ³`. -/
def Sphere2 : Type := {v : ℝ × ℝ × ℝ // v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2 = 1}

/-- The Bloch vector of a unit vector `(a, b) ∈ ℂ²`:
`(2 Re(conj a * b), 2 Im(conj a * b), |a|² - |b|²)`. -/
def blochVec (p : QubitState) : ℝ × ℝ × ℝ :=
  (2 * ((starRingEnd ℂ) p.1.1 * p.1.2).re, 2 * ((starRingEnd ℂ) p.1.1 * p.1.2).im,
    normSq p.1.1 - normSq p.1.2)

theorem blochVec_mem (p : QubitState) :
    (blochVec p).1 ^ 2 + (blochVec p).2.1 ^ 2 + (blochVec p).2.2 ^ 2 = 1 := by
  obtain ⟨⟨a, b⟩, h⟩ := p
  simp only [blochVec, normSq_apply] at h ⊢
  simp only [mul_re, mul_im, conj_re, conj_im]
  nlinarith [sq_nonneg (a.re * b.re), sq_nonneg (a.im * b.im), h]

/-- The Bloch map on unit vectors. -/
def blochOfState (p : QubitState) : Sphere2 := ⟨blochVec p, blochVec_mem p⟩

theorem blochOfState_phase_invariant {p q : QubitState} (h : PhaseRel p q) :
    blochOfState p = blochOfState q := by
  obtain ⟨u, hu, h1, h2⟩ := h
  have hconj : (starRingEnd ℂ) u * u = 1 := by
    rw [mul_comm, Complex.mul_conj, hu]
    norm_num
  have key : (starRingEnd ℂ) q.1.1 * q.1.2 = (starRingEnd ℂ) p.1.1 * p.1.2 := by
    rw [h1, h2, map_mul]
    calc (starRingEnd ℂ) u * (starRingEnd ℂ) p.1.1 * (u * p.1.2)
        = ((starRingEnd ℂ) u * u) * ((starRingEnd ℂ) p.1.1 * p.1.2) := by ring
      _ = (starRingEnd ℂ) p.1.1 * p.1.2 := by rw [hconj, one_mul]
  have hn1 : normSq q.1.1 = normSq p.1.1 := by rw [h1, map_mul, hu, one_mul]
  have hn2 : normSq q.1.2 = normSq p.1.2 := by rw [h2, map_mul, hu, one_mul]
  apply Subtype.ext
  show blochVec p = blochVec q
  simp only [blochVec]
  rw [key, hn1, hn2]

/-- The Bloch map from pure qubit states modulo phase to the 2-sphere. -/
def blochMap : PureQubit → Sphere2 :=
  Quotient.lift blochOfState fun _ _ h => blochOfState_phase_invariant h

/-- Two unit vectors with the same Bloch vector differ by a global phase. -/
theorem phaseRel_of_blochOfState_eq {p q : QubitState}
    (h : blochOfState p = blochOfState q) : PhaseRel p q := by
  obtain ⟨⟨a, b⟩, hp⟩ := p
  obtain ⟨⟨c, d⟩, hq⟩ := q
  have h' : blochVec ⟨(a, b), hp⟩ = blochVec ⟨(c, d), hq⟩ := congrArg Subtype.val h
  simp only [blochVec, Prod.mk.injEq] at h'
  obtain ⟨h1, h2, h3⟩ := h'
  simp only at hp hq h1 h2 h3
  have hab : (starRingEnd ℂ) a * b = (starRingEnd ℂ) c * d := by
    apply Complex.ext <;> linarith
  have hna : normSq a = normSq c := by linarith
  have hnb : normSq b = normSq d := by linarith
  by_cases ha : a = 0
  · have hc : c = 0 := by
      have : normSq c = 0 := by rw [← hna, ha]; simp
      exact normSq_eq_zero.mp this
    have hb1 : normSq b = 1 := by rw [ha] at hp; simpa using hp
    have hb0 : b ≠ 0 := by
      intro hb; rw [hb] at hb1; simp at hb1
    refine ⟨d / b, ?_, ?_, ?_⟩
    · rw [map_div₀, ← hnb, hb1]; simp
    · show c = _ * a
      rw [ha, hc, mul_zero]
    · show d = _ * b
      field_simp
  · have hna0 : normSq a ≠ 0 := fun h0 => ha (normSq_eq_zero.mp h0)
    have hconj : (starRingEnd ℂ) a ≠ 0 := by simpa using ha
    have hcb : c * b = a * d := by
      refine mul_left_cancel₀ hconj ?_
      calc (starRingEnd ℂ) a * (c * b) = c * ((starRingEnd ℂ) a * b) := by ring
        _ = c * ((starRingEnd ℂ) c * d) := by rw [hab]
        _ = (c * (starRingEnd ℂ) c) * d := by ring
        _ = ((normSq c : ℝ) : ℂ) * d := by rw [Complex.mul_conj]
        _ = ((normSq a : ℝ) : ℂ) * d := by rw [hna]
        _ = (a * (starRingEnd ℂ) a) * d := by rw [Complex.mul_conj]
        _ = (starRingEnd ℂ) a * (a * d) := by ring
    refine ⟨c / a, ?_, ?_, ?_⟩
    · rw [map_div₀, ← hna]
      field_simp
    · show c = _ * a
      field_simp
    · show d = _ * b
      field_simp
      linear_combination -hcb

theorem blochMap_injective : Function.Injective blochMap := by
  intro P Q h
  induction P using Quotient.inductionOn with
  | _ p =>
    induction Q using Quotient.inductionOn with
    | _ q =>
      exact Quotient.sound (phaseRel_of_blochOfState_eq h)

theorem blochMap_surjective : Function.Surjective blochMap := by
  rintro ⟨⟨x, y, z⟩, hv⟩
  simp only at hv
  by_cases hz : z = -1
  · have hx : x = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
    have hy : y = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
    refine ⟨Quotient.mk _ ⟨(0, 1), by simp⟩, ?_⟩
    apply Subtype.ext
    show blochVec ⟨(0, 1), _⟩ = (x, y, z)
    simp [blochVec, hx, hy, hz]
  · have hzge : -1 ≤ z := by nlinarith [sq_nonneg x, sq_nonneg y]
    have hz1 : -1 < z := lt_of_le_of_ne hzge (Ne.symm hz)
    set s : ℝ := Real.sqrt ((1 + z) / 2) with hs
    have hs0 : 0 < s := Real.sqrt_pos.mpr (by linarith)
    have hs2 : s * s = (1 + z) / 2 := by
      rw [hs, Real.mul_self_sqrt (by linarith : (0:ℝ) ≤ (1 + z) / 2)]
    have hs0' : s ≠ 0 := ne_of_gt hs0
    have hnorm : normSq (⟨s, 0⟩ : ℂ) + normSq (⟨x / (2 * s), y / (2 * s)⟩ : ℂ) = 1 := by
      simp only [normSq_apply]
      field_simp
      nlinarith [hs2, hv]
    refine ⟨Quotient.mk _ ⟨((⟨s, 0⟩ : ℂ), (⟨x / (2 * s), y / (2 * s)⟩ : ℂ)), hnorm⟩, ?_⟩
    apply Subtype.ext
    show blochVec ⟨((⟨s, 0⟩ : ℂ), (⟨x / (2 * s), y / (2 * s)⟩ : ℂ)), hnorm⟩ = (x, y, z)
    simp only [blochVec, normSq_apply, mul_re, mul_im, conj_re, conj_im, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · show 2 * (s * (x / (2 * s)) - -0 * (y / (2 * s))) = x
      field_simp
      ring
    · show 2 * (s * (y / (2 * s)) + -0 * (x / (2 * s))) = y
      field_simp
      ring
    · show s * s + 0 * 0 - (x / (2 * s) * (x / (2 * s)) + y / (2 * s) * (y / (2 * s))) = z
      field_simp
      nlinarith [hs2, hv]

/-- **Bloch sphere bijection**: pure qubit states modulo global phase are in
bijection with the points of the 2-sphere `S²`, via the Bloch map. -/
theorem bloch_sphere_bijection : Function.Bijective blochMap :=
  ⟨blochMap_injective, blochMap_surjective⟩

/-- The Bloch sphere bijection packaged as an equivalence `ℂP¹ ≃ S²`. -/
noncomputable def blochEquiv : PureQubit ≃ Sphere2 :=
  Equiv.ofBijective blochMap bloch_sphere_bijection

/-- `Sphere2` really is the unit sphere of the Euclidean space `ℝ³`. -/
def sphere2Equiv : Sphere2 ≃ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 where
  toFun v := ⟨!₂[v.1.1, v.1.2.1, v.1.2.2], by
    rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq, Real.sqrt_eq_one]
    simpa [Fin.sum_univ_three, sq_abs] using v.2⟩
  invFun w := ⟨(w.1 0, w.1 1, w.1 2), by
    have hw : ∑ i, ‖w.1 i‖ ^ 2 = 1 := by
      have h := w.2
      rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq, Real.sqrt_eq_one] at h
      exact h
    simpa [Fin.sum_univ_three, sq_abs] using hw⟩
  left_inv := by
    rintro ⟨⟨x, y, z⟩, h⟩
    apply Subtype.ext
    simp
  right_inv := by
    rintro ⟨v, h⟩
    apply Subtype.ext
    ext i
    fin_cases i <;> simp

/-- The same bijection, stated for the unit sphere of `EuclideanSpace ℝ (Fin 3)`. -/
noncomputable def blochEquivEuclidean :
    PureQubit ≃ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  blochEquiv.trans sphere2Equiv

end QC

