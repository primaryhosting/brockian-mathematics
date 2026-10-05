/-
  CompactCriterion.lean — an abstract compactness criterion: an operator whose
  unit-ball image is uniformly approximable by finite-dimensional subspaces is
  a compact operator.
-/
import Mathlib

open Metric Filter

namespace Brockian.Weyl.OscillatorCompact

/-- An operator whose closed-unit-ball image is uniformly approximable by
finite-dimensional subspaces is a compact operator. -/

theorem shiftedRange_closure_eq_top {T : H →ₗ.[ℂ] H} (hsym : IsSymmetric T)
    (hd : Dense (T.domain : Set H)) {z : ℂ}
    (hz : |z.im| = 1) (hdef : deficiencySpace T ((starRingEnd ℂ) z) = ⊥) :
    shiftedRange T.closure z = ⊤ := by
  have hclosedset := isClosed_shiftedRange_closure hsym hd hz
  haveI : CompleteSpace (shiftedRange T.closure z) :=
    hclosedset.completeSpace_coe
  have horth : (shiftedRange T.closure z)ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro g hg
    -- `g` is orthogonal to the smaller range of `T` itself
    have hsub : shiftedRange T z ≤ shiftedRange T.closure z := by
      intro y hy
      obtain ⟨v, hv⟩ := (mem_shiftedRange_iff T z y).mp hy
      have hmemw : (v : H) ∈ T.closure.domain := (T.le_closure).1 v.2
      have hval : T v = T.closure ⟨(v : H), hmemw⟩ := (T.le_closure).2 rfl
      exact (mem_shiftedRange_iff T.closure z y).mpr
        ⟨⟨(v : H), hmemw⟩, by rw [← hval]; exact hv⟩
    have hg' : g ∈ (shiftedRange T z)ᗮ := by
      intro u hu
      exact hg u (hsub hu)
    obtain ⟨hmem, hdefmem⟩ := mem_deficiencySpace_of_mem_orthogonal hd hg'
    rw [hdef, Submodule.mem_bot] at hdefmem
    exact congrArg Subtype.val hdefmem
  exact (Submodule.orthogonal_eq_bot_iff).mp horth

/-- Essential self-adjointness makes the shifted closure surjective. -/
