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

/-
The limit step of the transfinite construction: at a countable limit ordinal `a`
we build a nice partial injection with domain `a` coherent with all previous ones,
by an `ω`-recursion along a cofinal sequence, reserving one new value at each stage
so that the resulting function still omits infinitely many naturals.
-/
import RequestProject.Aronszajn.Step

open Ordinal Cardinal Set

namespace Aronszajn


theorem exists_step (a : Ordinal.{0}) (ha : a < ω₁) (d : Ordinal.{0} → Ordinal.{0} → ℕ)
    (hd : ∀ b < a, Nice b (d b) ∧ ∀ c < b, Coh (d b) (d c) c) :
    ∃ f, Nice a f ∧ ∀ b < a, Coh f (d b) b := by
  rcases eq_or_ne a 0 with rfl | ha0
  · exact ⟨fun _ => 0, nice_zero, fun b hb => absurd hb (by simp)⟩
  by_cases hsucc : ∃ b, a = b + 1
  · obtain ⟨b, rfl⟩ := hsucc
    have hb : b < b + 1 := Order.lt_add_one_iff.2 le_rfl
    obtain ⟨f, hfnice, hfagree⟩ := exists_succ_step (hd b hb).1
    refine ⟨f, hfnice, fun c hc => ?_⟩
    rw [Order.lt_add_one_iff] at hc
    have hagree : Coh f (d b) c := coh_of_eq fun e he => hfagree e (lt_of_lt_of_le he hc)
    rcases lt_or_eq_of_le hc with hc' | rfl
    · exact hagree.trans ((hd b hb).2 c hc')
    · exact hagree
  · have ha0' : 0 < a := lt_of_le_of_ne (by simp) (Ne.symm ha0)
    have halim : ∀ b < a, b + 1 < a := by
      intro b hb
      have h1 : b + 1 ≤ a := Order.add_one_le_iff.2 hb
      rcases lt_or_eq_of_le h1 with h | h
      · exact h
      · exact absurd ⟨b, h.symm⟩ hsucc
    exact exists_limit_step ha ha0' halim hd

open Classical in
/-- The choice of the next function in the transfinite construction. -/
