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

/-!
# Bloch Sphere Bijection
Category: Quantum Computing
Target: QC.bloch_sphere_bijection
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

open Complex

/-- A pure qubit state: a unit vector in `ℂ²`. -/

theorem blochQuot_surjective : Function.Surjective blochQuot := by
  rintro ⟨⟨x, y, z⟩, hp⟩
  simp only at hp
  by_cases hz : z = -1
  · refine ⟨Quotient.mk _ ⟨(0, 1), by simp⟩, ?_⟩
    have hx : x = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
    have hy : y = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
    simp only [blochQuot, Quotient.lift_mk, bloch, Qubit.fst, Qubit.snd, Subtype.mk.injEq,
      Prod.mk.injEq]
    refine ⟨by simp [hx], by simp [hy], by simp [hz]⟩
  · have hz1 : (1 : ℝ) + z > 0 := by
      rcases lt_trichotomy z (-1) with h | h | h
      · nlinarith [sq_nonneg x, sq_nonneg y]
      · exact absurd h hz
      · linarith
    set a : ℝ := Real.sqrt ((1 + z) / 2) with ha
    have ha2 : a ^ 2 = (1 + z) / 2 := Real.sq_sqrt (by linarith)
    have hapos : 0 < a := Real.sqrt_pos.mpr (by linarith)
    refine ⟨Quotient.mk _ ⟨((a : ℂ), (x / (2 * a) : ℝ) + (y / (2 * a) : ℝ) * Complex.I), ?_⟩, ?_⟩
    · simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
      have hane : a ≠ 0 := ne_of_gt hapos
      field_simp
      nlinarith [ha2, hp]
    · simp only [blochQuot, Quotient.lift_mk, bloch, Qubit.fst, Qubit.snd, Subtype.mk.injEq,
        Prod.mk.injEq, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
        Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, Complex.normSq_apply]
      have hane : a ≠ 0 := ne_of_gt hapos
      refine ⟨by field_simp; ring, by field_simp; ring, ?_⟩
      field_simp
      nlinarith [ha2, hp]

/-- **Bloch sphere bijection**: pure qubit states modulo global phase are in bijection with
the points of the two-sphere `S²`. -/
