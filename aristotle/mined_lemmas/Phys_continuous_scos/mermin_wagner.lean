import Mathlib

/-!
# The circle-valued spin space

The spin space of the classical XY model is the circle `Spin = ℝ / 2πℤ`, a compact
abelian group carrying a translation invariant (Haar) measure.  This file sets up the
cosine and sine functions on `Spin` together with the elementary trigonometric facts
used in the Mermin–Wagner argument.
-/

namespace Phys

noncomputable section

open MeasureTheory

instance factTwoPi : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- The spin space: the circle `ℝ / 2πℤ`. -/
abbrev Spin := AddCircle (2 * Real.pi)

/-- The cosine function on the circle. -/

theorem mermin_wagner {d : ℕ} (hd : d ≤ 2) {β : ℝ} (hβ : 0 < β) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℕ, ∀ N, R ≤ N → ∀ τ : Site d → Spin,
      |magCos β N τ| < ε ∧ |magSin β N τ| < ε := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  obtain ⟨R, hR1, hR⟩ := dirichletEnergy_small (d := d) hd
    (ε := 2 * ε ^ 2 / (β * Real.pi ^ 2)) (by positivity)
  refine ⟨R, fun N hN τ => ?_⟩
  -- the spin-wave profile
  set f : Site d → ℝ := fun x => Real.pi * spinWave R x with hf
  have hsupp : ∀ x, x ∉ box d N → f x = 0 := by
    intro x hx
    have hxn : N < snorm x := by
      by_contra hcon
      exact hx (mem_box_iff.2 (by omega))
    have : spinWave R x = 0 := spinWave_eq_zero_of_le hR1 (by omega)
    simp [hf, this]
  set g : BoxCfg d N := shiftOf N f with hg
  -- the energy cost of the spin wave
  set K : ℝ := ∑ x ∈ box d (N + 1), ∑ i : Fin d, (f x - f (x + unitVec i)) ^ 2 with hK
  have hKeq : K = Real.pi ^ 2 * dirichletEnergy (d := d) R N := by
    rw [hK, dirichletEnergy, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [hf]
    ring
  have hK0 : 0 ≤ K := by
    rw [hK]
    exact Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hEsmall : dirichletEnergy (d := d) R N < 2 * ε ^ 2 / (β * Real.pi ^ 2) := hR N hN
  have hKsmall : 2 * β * K < 4 * ε ^ 2 := by
    rw [hKeq]
    have h1 : Real.pi ^ 2 * dirichletEnergy (d := d) R N
        < Real.pi ^ 2 * (2 * ε ^ 2 / (β * Real.pi ^ 2)) := by
      exact mul_lt_mul_of_pos_left hEsmall (by positivity)
    have h2 : Real.pi ^ 2 * (2 * ε ^ 2 / (β * Real.pi ^ 2)) = 2 * ε ^ 2 / β := by
      field_simp
    rw [h2] at h1
    have h3 : 2 * β * (Real.pi ^ 2 * dirichletEnergy (d := d) R N) < 2 * β * (2 * ε ^ 2 / β) := by
      exact mul_lt_mul_of_pos_left h1 (by positivity)
    have h4 : 2 * β * (2 * ε ^ 2 / β) = 4 * ε ^ 2 := by field_simp; ring
    linarith
  have hsqrt : Real.sqrt (2 * β * K) < 2 * ε := by
    have : Real.sqrt (2 * β * K) < Real.sqrt (4 * ε ^ 2) := by
      apply Real.sqrt_lt_sqrt (by positivity) hKsmall
    have h4 : Real.sqrt (4 * ε ^ 2) = 2 * ε := by
      rw [show (4:ℝ) * ε ^ 2 = (2 * ε) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    linarith [this, h4.le, h4.ge]
  have hcost : ∀ θ : BoxCfg d N,
      xyHam N τ (θ + g) + xyHam N τ (θ - g) - 2 * xyHam N τ θ ≤ K :=
    fun θ => xyHam_second_diff N τ f hsupp θ
  have hf0 : f (0 : Site d) = Real.pi := by simp [hf, spinWave_origin]
  -- the key identity: the spin wave rotates the spin at the origin by π
  have hrot : ∀ θ : BoxCfg d N, extend N τ (θ + g) (0 : Site d)
      = extend N τ θ (0 : Site d) + ((Real.pi : ℝ) : Spin) := by
    intro θ
    rw [hg, extend_add_shift N τ f hsupp θ 0, hf0]
  constructor
  · -- cosine component
    have hbound := gibbs_shift_bound β hβ.le (xyHam N τ) (continuous_xyHam N τ)
      (fun θ => scos (extend N τ θ (0 : Site d)))
      (continuous_scos.comp (continuous_extend_apply N τ 0)) 1
      (fun θ => abs_scos_le_one _) g K hK0 hcost
    have hneg : (fun θ : BoxCfg d N => scos (extend N τ (θ + g) (0 : Site d)))
        = fun θ : BoxCfg d N => -scos (extend N τ θ (0 : Site d)) := by
      funext θ
      rw [hrot θ, scos_add_pi]
    rw [hneg, gAvg_neg] at hbound
    have : |(-magCos β N τ) - magCos β N τ| ≤ 1 * Real.sqrt (2 * β * K) := hbound
    have h2 : 2 * |magCos β N τ| ≤ Real.sqrt (2 * β * K) := by
      have habs : |(-magCos β N τ) - magCos β N τ| = 2 * |magCos β N τ| := by
        rw [show (-magCos β N τ) - magCos β N τ = -(2 * magCos β N τ) by ring, abs_neg, abs_mul]
        norm_num
      linarith [habs.symm ▸ this]
    linarith
  · -- sine component
    have hbound := gibbs_shift_bound β hβ.le (xyHam N τ) (continuous_xyHam N τ)
      (fun θ => ssin (extend N τ θ (0 : Site d)))
      (continuous_ssin.comp (continuous_extend_apply N τ 0)) 1
      (fun θ => abs_ssin_le_one _) g K hK0 hcost
    have hneg : (fun θ : BoxCfg d N => ssin (extend N τ (θ + g) (0 : Site d)))
        = fun θ : BoxCfg d N => -ssin (extend N τ θ (0 : Site d)) := by
      funext θ
      rw [hrot θ, ssin_add_pi]
    rw [hneg, gAvg_neg] at hbound
    have : |(-magSin β N τ) - magSin β N τ| ≤ 1 * Real.sqrt (2 * β * K) := hbound
    have h2 : 2 * |magSin β N τ| ≤ Real.sqrt (2 * β * K) := by
      have habs : |(-magSin β N τ) - magSin β N τ| = 2 * |magSin β N τ| := by
        rw [show (-magSin β N τ) - magSin β N τ = -(2 * magSin β N τ) by ring, abs_neg, abs_mul]
        norm_num
      linarith [habs.symm ▸ this]
    linarith

end

end Phys

import Mathlib

/-!
# The lattice `ℤ^d`, spin waves, and the Dirichlet energy in dimension `d ≤ 2`

This file contains the geometric heart of the Mermin–Wagner theorem: in dimension
`d ≤ 2` there are "spin waves", i.e. functions equal to `1` at the origin and vanishing
outside a finite box, whose Dirichlet energy is arbitrarily small.  (This is the lattice
counterpart of the recurrence of the simple random walk in dimensions `≤ 2`.)

The spin wave used is the logarithmic profile
`f R x = max 0 (1 - log (1 + ‖x‖) / log (1 + R))`, whose Dirichlet energy is `O(1 / log R)`.
-/

namespace Phys

noncomputable section

open Finset

variable {d : ℕ}

/-- The sites of the lattice `ℤ^d`. -/
abbrev Site (d : ℕ) := Fin d → ℤ

/-- The sup-norm of a lattice site. -/
