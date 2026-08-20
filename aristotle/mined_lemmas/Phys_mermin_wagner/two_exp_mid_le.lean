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

lemma two_exp_mid_le (u v : ℝ) : 2 * Real.exp ((u + v) / 2) ≤ Real.exp u + Real.exp v := by
  have h := two_mul_le_add_sq (Real.exp (u / 2)) (Real.exp (v / 2))
  have hu : Real.exp (u / 2) ^ 2 = Real.exp u := by
    rw [sq, ← Real.exp_add]; ring_nf
  have hv : Real.exp (v / 2) ^ 2 = Real.exp v := by
    rw [sq, ← Real.exp_add]; ring_nf
  have huv : Real.exp (u / 2) * Real.exp (v / 2) = Real.exp ((u + v) / 2) := by
    rw [← Real.exp_add]; ring_nf
  rw [hu, hv] at h
  calc 2 * Real.exp ((u + v) / 2) = 2 * Real.exp (u / 2) * Real.exp (v / 2) := by
        rw [mul_assoc, huv]
    _ ≤ Real.exp u + Real.exp v := h

/-- **Key inequality.**  If shifting a configuration by `± w` raises the energy, in second
difference, by at most `K`, then the Gibbs average of a nonnegative observable is almost
convex along the shift.  This is the finite–volume form of the spin–wave (Mermin–Wagner)
argument: it uses only translation invariance of the a priori measure. -/
