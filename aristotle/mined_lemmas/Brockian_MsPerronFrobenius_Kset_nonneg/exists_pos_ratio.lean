import Mathlib

namespace Brockian.MsPerronFrobenius

open Matrix Finset

/-- Probability vectors all of whose coordinates are at least `δ`. -/

lemma exists_pos_ratio (hn : 0 < n) (hpos : ∀ i j, 0 < M i j) {δ : ℝ} (hδ : 0 < δ)
    {x : Fin n → ℝ} (hx : x ∈ Kset n δ) : ∃ t : ℝ, 0 < t ∧ ∀ i, t * x i ≤ M.mulVec x i := by
  have hxpos : ∀ i, 0 < x i := fun i => lt_of_lt_of_le hδ (hx.1 i)
  have hxne : x ≠ 0 := Kset_ne_zero hx
  have hMxpos : ∀ i, 0 < M.mulVec x i :=
    fun i => mulVec_pos hpos (fun i => (hxpos i).le) hxne i
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  refine ⟨Finset.univ.inf' hne (fun i => M.mulVec x i / x i), ?_, fun i => ?_⟩
  · rw [Finset.lt_inf'_iff]
    exact fun i _ => div_pos (hMxpos i) (hxpos i)
  · have h : Finset.univ.inf' hne (fun i => M.mulVec x i / x i) ≤ M.mulVec x i / x i :=
      Finset.inf'_le _ (Finset.mem_univ i)
    rwa [le_div_iff₀ (hxpos i)] at h

/-- From a strict componentwise gap one extracts a uniform improvement `ε`. -/
