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


theorem exists_succ_step {b : Ordinal.{0}} {h : Ordinal.{0} → ℕ} (hh : Nice b h) :
    ∃ f, Nice (b + 1) f ∧ ∀ e < b, f e = h e := by
  classical
  obtain ⟨hinj, hnorm, hcoinf⟩ := hh
  obtain ⟨r, hr⟩ := hcoinf.nonempty
  refine ⟨fun e => if e < b then h e else if e = b then r else 0, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro e he f hf hef
    rw [Order.lt_add_one_iff] at he hf
    rcases lt_or_eq_of_le he with he' | rfl
    · rcases lt_or_eq_of_le hf with hf' | rfl
      · simpa [he', hf'] using hinj e he' f hf' (by simpa [he', hf'] using hef)
      · simp only [he', if_true, lt_irrefl, if_false] at hef
        exact absurd hef (hr e he')
    · rcases lt_or_eq_of_le hf with hf' | rfl
      · simp only [hf', if_true, lt_irrefl, if_false] at hef
        exact absurd hef.symm (hr f hf')
      · rfl
  · intro e hbe
    have h1 : ¬ e < b := not_lt.2 (le_trans (le_of_lt (Order.lt_add_one_iff.2 le_rfl)) hbe)
    have h2 : e ≠ b := by
      intro hEq
      exact absurd (hEq ▸ hbe) (not_le.2 (Order.lt_add_one_iff.2 le_rfl))
    simp [h1, h2]
  · have hsub : ({n : ℕ | ∀ e < b, h e ≠ n} \ {r}) ⊆
        {n : ℕ | ∀ e < b + 1, (if e < b then h e else if e = b then r else 0) ≠ n} := by
      rintro n ⟨hn, hnr⟩ e he
      rw [Order.lt_add_one_iff] at he
      rcases lt_or_eq_of_le he with he' | rfl
      · simpa [he'] using hn e he'
      · simp only [lt_irrefl, if_false]
        intro hEq
        exact hnr (by simp [← hEq])
    exact Set.Infinite.mono hsub (hcoinf.diff (Set.finite_singleton r))
  · intro e he; simp [he]

/-! ### Cofinal sequences in countable limit ordinals -/

