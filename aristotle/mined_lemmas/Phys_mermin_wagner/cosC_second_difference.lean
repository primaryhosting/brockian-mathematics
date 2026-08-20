/-
The classical XY model on a finite graph, and the finite-volume Mermin-Wagner bound
on its magnetization in terms of the Dirichlet energy of a spin-wave profile.
-/
import RequestProject.Core

open MeasureTheory Real

namespace Phys

noncomputable section

variable {S ι : Type} [Fintype S]

/-- The energy of the classical XY model on a finite graph whose edges are indexed by
`bonds`, with endpoints `src` and `tgt`, coupling `J` and external field `h`. -/

lemma cosC_second_difference (z : Circ) (s : ℝ) :
    -(s ^ 2) ≤ cosC (z + ((s : ℝ) : Circ)) + cosC (z - ((s : ℝ) : Circ)) - 2 * cosC z := by
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective (s := AddSubgroup.zmultiples (2 * Real.pi)) z
  have h1 : ((a : ℝ) : Circ) + ((s : ℝ) : Circ) = ((a + s : ℝ) : Circ) := rfl
  have h2 : ((a : ℝ) : Circ) - ((s : ℝ) : Circ) = ((a - s : ℝ) : Circ) := rfl
  show -(s ^ 2) ≤ cosC (((a : ℝ) : Circ) + _) + cosC (((a : ℝ) : Circ) - _) - 2 * cosC ((a : ℝ) : Circ)
  rw [h1, h2, cosC_coe, cosC_coe, cosC_coe]
  have hc : Real.cos (a + s) + Real.cos (a - s) = 2 * Real.cos a * Real.cos s := by
    rw [Real.cos_add, Real.cos_sub]; ring
  rw [hc]
  have h3 : 1 - s ^ 2 / 2 ≤ Real.cos s := one_sub_sq_div_two_le_cos
  have h4 : Real.cos s ≤ 1 := Real.cos_le_one s
  have h5 : |Real.cos a| ≤ 1 := Real.abs_cos_le_one a
  have h6 : -1 ≤ Real.cos a := (abs_le.mp h5).1
  have h7 : Real.cos a ≤ 1 := (abs_le.mp h5).2
  nlinarith [sq_nonneg s, sq_nonneg (Real.cos a - 1), sq_nonneg (Real.cos a + 1)]

