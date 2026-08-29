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

