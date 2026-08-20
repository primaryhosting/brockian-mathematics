import Mathlib
namespace Brockian.MsGaussLucas

open Polynomial

/-- The conjugate of `u⁻¹` is the positive real multiple `(normSq u)⁻¹` of `u`. -/

private lemma mem_convexHull_of_sum_inv_eq_zero {n : ℕ} (hn : 0 < n) (r : Fin n → ℂ) (z : ℂ)
    (hne : ∀ i, z ≠ r i) (hsum : ∑ i, (z - r i)⁻¹ = 0) :
    z ∈ convexHull ℝ (Set.range r) := by
  classical
  set w : Fin n → ℝ := fun i => (Complex.normSq (z - r i))⁻¹ with hw
  have hwpos : ∀ i, 0 < w i := by
    intro i
    have : z - r i ≠ 0 := sub_ne_zero.mpr (hne i)
    simpa [hw] using inv_pos.mpr (Complex.normSq_pos.mpr this)
  have hW : 0 < ∑ i, w i :=
    Finset.sum_pos (fun i _ => hwpos i) (Finset.univ_nonempty_iff.mpr
      (Fin.pos_iff_nonempty.mp hn))
  have hzero : ∑ i, w i • (z - r i) = 0 := sum_normSq_inv_smul_eq_zero r z hsum
  have hkey : (Finset.univ : Finset (Fin n)).centerMass w r = z := by
    have h1 : (∑ i, w i) • z = ∑ i, w i • r i := by
      have : (∑ i, w i • z) - (∑ i, w i • r i) = 0 := by
        rw [← Finset.sum_sub_distrib]
        simpa [smul_sub] using hzero
      rw [Finset.sum_smul]
      linear_combination (norm := module) this
    rw [Finset.centerMass, ← h1, inv_smul_smul₀ (ne_of_gt hW)]
  rw [← hkey]
  exact Finset.centerMass_mem_convexHull _ (fun i _ => (hwpos i).le) hW
    (fun i _ => Set.mem_range_self i)

/-- Every nonzero complex polynomial factors as a constant times a product of linear factors,
indexed by `Fin p.natDegree`. -/
