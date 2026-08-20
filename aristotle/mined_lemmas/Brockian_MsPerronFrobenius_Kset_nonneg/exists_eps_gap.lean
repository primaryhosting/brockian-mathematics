import Mathlib

namespace Brockian.MsPerronFrobenius

open Matrix Finset

/-- Probability vectors all of whose coordinates are at least `δ`. -/

lemma exists_eps_gap (hn : 0 < n) {r : ℝ} {u : Fin n → ℝ} (hu : ∀ i, 0 < u i)
    (hgap : ∀ i, r * u i < M.mulVec u i) :
    ∃ ε > 0, ∀ i, (r + ε) * u i ≤ M.mulVec u i := by
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  set e := fun i => (M.mulVec u i - r * u i) / u i with he
  have he_pos_all : ∀ i, 0 < e i := fun i => div_pos (sub_pos.mpr (hgap i)) (hu i)
  obtain ⟨i₀, -, hmin⟩ := Finset.exists_min_image Finset.univ e Finset.univ_nonempty
  refine ⟨e i₀, he_pos_all i₀, fun i => ?_⟩
  have h1 : e i₀ * u i ≤ e i * u i :=
    mul_le_mul_of_nonneg_right (hmin i (Finset.mem_univ i)) (hu i).le
  have h2 : e i * u i = M.mulVec u i - r * u i := div_mul_cancel₀ _ (ne_of_gt (hu i))
  nlinarith [h1, h2]

/-- If `M v ≥ r v` but `M v ≠ r v`, then the normalized image of `v` gives a strictly better
ratio. -/
