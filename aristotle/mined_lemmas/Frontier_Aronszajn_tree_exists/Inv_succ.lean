import Mathlib
/-!
# Aronszajn Tree Exists
Category: Frontier — Set Theory
Target: Frontier.Aronszajn_tree_exists
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

open Set Cardinal Ordinal
open scoped Ordinal Cardinal

namespace Frontier

/-! ## Countable ordinals -/

/-- The set of ordinals below `a` is countable exactly when `a < ω₁`. -/

theorem Inv_succ {a : Ordinal.{0}} (ha : Inv a) : Inv (Order.succ a) := by
  have key : ∀ ξ : Ordinal.{0}, ξ < a → E (Order.succ a) ξ = E a ξ := by
    intro ξ hξ
    rw [E_succ, succStep, if_pos hξ]
  refine ⟨?_, ?_, ?_⟩
  · intro ξ hξ
    have : ¬ ξ < a := fun h => absurd (h.trans_le (Order.le_succ a)) (not_lt.2 hξ)
    rw [E_succ, succStep, if_neg this]
  · intro k
    refine Set.Finite.subset ((ha.2.1 k).union (Set.finite_singleton a)) ?_
    rintro ξ ⟨h1, h2⟩
    rcases lt_or_eq_of_le (Order.lt_succ_iff.1 h1) with h | h
    · exact Or.inl ⟨h, by rwa [key ξ h] at h2⟩
    · exact Or.inr h
  · intro b hb
    have hba : b ≤ a := Order.lt_succ_iff.1 hb
    rcases lt_or_eq_of_le hba with h | h
    · refine Set.Finite.subset (ha.2.2 b h) ?_
      rintro ξ ⟨h1, h2⟩
      exact ⟨h1, by rwa [key ξ (h1.trans h)] at h2⟩
    · subst h
      convert Set.finite_empty
      ext ξ
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_not]
      intro hξ
      exact key ξ hξ

