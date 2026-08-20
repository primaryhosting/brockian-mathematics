import Mathlib
import RequestProject.Brun.Final

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

/-- **Brun's theorem**: the sum of the reciprocals of the twin primes converges.

The twin primes are indexed by the subtype of naturals `p` such that both `p` and `p + 2`
are prime, and the summand is `1 / p`. -/

lemma bonferroni_sets {α : Type*} [DecidableEq α] (P : Finset α) (Q : α → Prop)
    [DecidablePred Q] (k : ℕ) (hk : Even k) :
    (if ∀ p ∈ P, ¬ Q p then (1 : ℝ) else 0)
      ≤ ∑ j ∈ range (k + 1), (-1 : ℝ) ^ j *
          (((P.powersetCard j).filter (fun S => ∀ p ∈ S, Q p)).card : ℝ) := by
  have hfilter : ∀ j, (P.powersetCard j).filter (fun S => ∀ p ∈ S, Q p)
      = (P.filter Q).powersetCard j := by
    intro j
    ext S
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨hSP, hcard⟩, hQ⟩
      exact ⟨fun x hx => Finset.mem_filter.mpr ⟨hSP hx, hQ x hx⟩, hcard⟩
    · rintro ⟨hSP, hcard⟩
      refine ⟨⟨fun x hx => (Finset.mem_filter.mp (hSP hx)).1, hcard⟩, ?_⟩
      exact fun x hx => (Finset.mem_filter.mp (hSP hx)).2
  have hcard : ∀ j, (((P.powersetCard j).filter (fun S => ∀ p ∈ S, Q p)).card : ℝ)
      = ((P.filter Q).card.choose j : ℝ) := by
    intro j; rw [hfilter j, Finset.card_powersetCard]
  simp only [hcard]
  have hkey := bonferroni_choose (P.filter Q).card k hk
  refine le_trans ?_ hkey
  by_cases h : ∀ p ∈ P, ¬ Q p
  · rw [if_pos h, if_pos]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    exact h
  · rw [if_neg h]
    split <;> norm_num

end Brun

import RequestProject.Brun.Asymptotics
import RequestProject.Brun.Dyadic

/-!
# Brun's theorem

Combining the dyadic decomposition with the asymptotic bound for `twinCount (2^m)`
we obtain the summability of the twin prime indicator series `∑ 1/p`.
-/

namespace Brun

/-- The dyadic input needed for `summable_twinIndicator`. -/
