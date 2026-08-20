/-
# Boundary Term Vanishes
Category: Gate1 Operator
Target: Brockian.DilationGenerator.boundary_term_vanishes
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Boundary Term Vanishes
Category: Gate1 Operator
Target: Brockian.DilationGenerator.boundary_term_vanishes
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian
namespace DilationGenerator

open Filter Set Topology

/-- A compact subset of `(0, ∞)` is bounded away from `0`: there is `ε > 0` such that no
point below `ε` belongs to the set. -/
lemma exists_pos_lt_notMem_of_compact_subset_Ioi {S : Set ℝ} (hS : IsCompact S)
    (hsub : S ⊆ Set.Ioi (0 : ℝ)) : ∃ ε > (0 : ℝ), ∀ x < ε, x ∉ S := by
  rcases S.eq_empty_or_nonempty with h | h
  · exact ⟨1, one_pos, fun x _ => by simp [h]⟩
  · obtain ⟨a, haS, hmin⟩ := hS.exists_isMinOn h continuousOn_id
    refine ⟨a, hsub haS, fun x hx hxS => ?_⟩
    exact absurd (hmin hxS) (not_le.mpr hx)

/-- A compact set of reals is bounded above: there is `M` such that no point above `M`
belongs to the set. -/
lemma exists_gt_notMem_of_compact {S : Set ℝ} (hS : IsCompact S) :
    ∃ M : ℝ, ∀ x > M, x ∉ S := by
  rcases S.eq_empty_or_nonempty with h | h
  · exact ⟨0, fun x _ => by simp [h]⟩
  · obtain ⟨a, haS, hmax⟩ := hS.exists_isMaxOn h continuousOn_id
    exact ⟨a, fun x hx hxS => absurd (hmax hxS) (not_le.mpr hx)⟩

variable {f g : ℝ → ℂ}

/-- For `f, g` with compact support contained in `(0, ∞)`, the boundary expression
`x * f x * conj (g x)` vanishes identically near `0` and near `+∞`; hence it tends to `0`
both as `x → 0⁺` and as `x → ∞`.

The hypotheses `hg`, `hg0` on `g` are kept because they are part of the requested statement,
but they turn out to be unnecessary: the compact support of `f` inside `(0, ∞)` already forces
the product to vanish near `0` and near `+∞`. -/
theorem boundary_term_vanishes
    (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    (hf0 : tsupport f ⊆ Set.Ioi (0 : ℝ)) (hg0 : tsupport g ⊆ Set.Ioi (0 : ℝ)) :
    Filter.Tendsto (fun x : ℝ => (x : ℂ) * f x * (starRingEnd ℂ) (g x))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (fun x : ℝ => (x : ℂ) * f x * (starRingEnd ℂ) (g x))
        Filter.atTop (nhds 0) := by
  obtain ⟨ε, hε, hlow⟩ := exists_pos_lt_notMem_of_compact_subset_Ioi hf hf0
  obtain ⟨M, hhigh⟩ := exists_gt_notMem_of_compact hf
  constructor
  · refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    have h : ∀ᶠ x : ℝ in nhds (0 : ℝ), x < ε :=
      Filter.eventually_of_mem (Iio_mem_nhds hε) (fun x hx => hx)
    filter_upwards [h.filter_mono nhdsWithin_le_nhds] with x hx
    simp [image_eq_zero_of_notMem_tsupport (hlow x hx)]
  · refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Filter.eventually_gt_atTop M] with x hx
    simp [image_eq_zero_of_notMem_tsupport (hhigh x hx)]

end DilationGenerator
end Brockian


