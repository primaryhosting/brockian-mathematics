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
