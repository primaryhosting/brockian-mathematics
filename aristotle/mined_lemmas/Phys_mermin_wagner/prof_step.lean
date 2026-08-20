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

lemma prof_step {R : ℕ} (hR : 1 ≤ R) (m : ℕ) :
    prof R m - prof R (m + 1) ≤ 1 / ((m + 1 : ℝ) * harm R) := by
  have hH := harm_pos hR
  have hkey : (1 - harm (m + 1) / harm R) ≤ (1 - harm m / harm R) := by
    have hmm : harm m ≤ harm (m + 1) := harm_mono (Nat.le_succ m)
    have h2 : harm m / harm R ≤ harm (m + 1) / harm R := by gcongr
    linarith
  have := max_sub_max_le hkey
  have hdiff : (1 - harm m / harm R) - (1 - harm (m + 1) / harm R)
      = 1 / ((m + 1 : ℝ) * harm R) := by
    rw [harm_succ]
    field_simp
    ring
  unfold prof
  linarith [hdiff ▸ this]

/-- The profile is `1`-Lipschitz at scale `1 / (m · harm R)`. -/
