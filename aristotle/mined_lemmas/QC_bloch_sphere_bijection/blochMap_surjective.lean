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
