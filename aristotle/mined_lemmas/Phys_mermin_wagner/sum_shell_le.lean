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

lemma sum_shell_le {d L : ℕ} (hd : d ≤ 2) (psi : ℕ → ℝ) (hpsi : ∀ m, 0 ≤ psi m) :
    ∑ x : Site d L, psi (rad x) ≤ ∑ m ∈ Finset.range (L + 1), (12 * m + 1 : ℝ) * psi m := by
  classical
  have hmaps : ∀ x : Site d L, x ∈ (Finset.univ : Finset (Site d L)) →
      rad x ∈ Finset.range (L + 1) := by
    intro x _
    simp only [Finset.mem_range]
    have := rad_le x
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_le_sum fun m _ => ?_
  have hcong : ∀ x ∈ Finset.univ.filter (fun x : Site d L => rad x = m), psi (rad x) = psi m := by
    intro x hx
    simp only [Finset.mem_filter] at hx
    rw [hx.2]
  rw [Finset.sum_congr rfl hcong, Finset.sum_const, nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ (hpsi m)
  exact_mod_cast Nat.cast_le.mpr (card_shell_le (L := L) hd m)

end Shells

end

end Phys

