import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace RiemannScaffold

noncomputable def riemannXi (s : ℂ) : ℂ := s * (s - 1) * completedRiemannZeta s

lemma riemannXi_apply (s : ℂ) : riemannXi s = s * (s - 1) * completedRiemannZeta s := rfl

end RiemannScaffold

theorem RiemannScaffold.riemannXi_eq_zero_of_nontrivial_zeta_zero {s : ℂ}
    (h : riemannZeta s = 0) (htriv : ¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) (hs1 : s ≠ 1) :
    RiemannScaffold.riemannXi s = 0 := by
  by_cases hs0 : s = 0
  · subst hs0; simp [RiemannScaffold.riemannXi]
  · rw [riemannZeta_def_of_ne_zero hs0] at h
    have hΛ : completedRiemannZeta s = 0 := by
      rcases div_eq_zero_iff.mp h with h' | h'
      · exact h'
      · exfalso
        obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp h'
        rcases Nat.eq_zero_or_pos n with rfl | hpos
        · simp at hn; exact hs0 hn
        · refine htriv ⟨n - 1, ?_⟩
          have hle : (1 : ℕ) ≤ n := hpos
          rw [hn]
          push_cast [Nat.cast_sub hle]
          ring
    simp [RiemannScaffold.riemannXi, hΛ]
