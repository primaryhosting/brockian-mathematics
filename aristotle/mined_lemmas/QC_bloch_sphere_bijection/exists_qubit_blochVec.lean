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

import Mathlib
/-!
# Bloch Sphere Bijection
Category: Quantum Computing
Target: QC.bloch_sphere_bijection
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex

namespace QC

/-- A pure state of a qubit: a unit vector `(a, b)` in `ℂ²`. -/
structure Qubit where
  a : ℂ
  b : ℂ
  unit : normSq a + normSq b = 1

/-- Two pure qubit states are equivalent when they differ by a global phase. -/

lemma exists_qubit_blochVec (x y z : ℝ) (h : x ^ 2 + y ^ 2 + z ^ 2 = 1) :
    ∃ v : Qubit, blochVec v = !₂[x, y, z] := by
  by_cases hz : z = -1
  · have hxy : x = 0 ∧ y = 0 := by
      constructor <;> nlinarith [sq_nonneg x, sq_nonneg y]
    exact ⟨⟨0, 1, by simp⟩, by simp [blochVec, hxy.1, hxy.2, hz]⟩
  · have hz1 : (0:ℝ) < 1 + z := by
      rcases lt_trichotomy (1 + z) 0 with hlt | heq | hgt
      · nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg (1 + z)]
      · exact absurd (by linarith : z = -1) hz
      · exact hgt
    set r := Real.sqrt ((1 + z) / 2) with hrdef
    have hr2 : r ^ 2 = (1 + z) / 2 := Real.sq_sqrt (by linarith)
    have hr0 : 0 < r := Real.sqrt_pos.mpr (by linarith)
    refine ⟨⟨⟨r, 0⟩, ⟨x / (2 * r), -(y / (2 * r))⟩, ?_⟩, ?_⟩
    · simp only [Complex.normSq_apply]
      field_simp
      nlinarith [hr2, h]
    · have hA : 2 * ((⟨r, 0⟩ : ℂ) * (starRingEnd ℂ) (⟨x / (2 * r), -(y / (2 * r))⟩ : ℂ)).re = x := by
        simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
        field_simp; ring
      have hB : 2 * ((⟨r, 0⟩ : ℂ) * (starRingEnd ℂ) (⟨x / (2 * r), -(y / (2 * r))⟩ : ℂ)).im = y := by
        simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
        field_simp; ring
      have hC : normSq (⟨r, 0⟩ : ℂ) - normSq (⟨x / (2 * r), -(y / (2 * r))⟩ : ℂ) = z := by
        simp only [Complex.normSq_apply]
        field_simp
        nlinarith [hr2, h]
      simp only [blochVec, hA, hB, hC]

