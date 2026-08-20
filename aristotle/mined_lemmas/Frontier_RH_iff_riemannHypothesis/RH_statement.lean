import Mathlib

/-!
# RH Statement
Category: Frontier — Moonshot
Target: Frontier.RH_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Frontier

open Complex

/-- A *trivial zero* of the Riemann zeta function is one of the points `-2, -4, -6, …`. -/

theorem RH_statement :
    RiemannHypothesis ↔ ∀ s : ℂ, riemannZeta s = 0 → s.re ≤ 1 / 2 := by
  rw [← RH_iff_riemannHypothesis]
  constructor
  · intro h s hz
    by_cases ht : IsTrivialZero s
    · have := re_le_neg_two_of_isTrivialZero ht
      linarith
    · by_cases h1 : s = 1
      · subst h1
        exact absurd hz (zeta_ne_zero_of_one_le_re (by simp))
      · exact le_of_eq (h s ⟨hz, ht, h1⟩)
  · intro h s hs
    have h1 := h s hs.1
    refine le_antisymm h1 ?_
    by_contra hlt
    push_neg at hlt
    have h2 := h _ (isNontrivialZero_one_sub hs).1
    simp only [Complex.sub_re, Complex.one_re] at h2
    linarith

end Frontier

