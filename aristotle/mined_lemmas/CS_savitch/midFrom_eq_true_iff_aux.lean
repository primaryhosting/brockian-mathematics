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

import RequestProject.Savitch.Machine

/-!
# Reduction to single-target reachability

`CS.addSink M` adds one new configuration (the *sink*) to `M`, with an edge from every
accepting configuration of `M` to the sink and no outgoing edge from the sink.  Then `M`
accepts iff the sink is reachable from the start configuration of `addSink M`, so that
deciding acceptance becomes deciding reachability between two *fixed* configurations.
-/

namespace CS

namespace Machine

/-- Add a sink configuration reachable exactly from the accepting configurations. -/

theorem midFrom_eq_true_iff_aux {n : ℕ} (R : Fin n → Fin n → Bool) (a b : Fin n) (j : ℕ) :
    ∀ i, n ≤ i + j →
      (midFrom R a b i = true ↔ ∃ m : Fin n, i ≤ m.val ∧ R a m = true ∧ R m b = true) := by
  induction j with
  | zero =>
      intro i hi
      rw [midFrom_of_ge R a b (by omega)]
      simp only [false_iff, Bool.false_eq_true, not_exists]
      rintro m ⟨hm, -, -⟩
      omega
  | succ j ih =>
      intro i hi
      by_cases h : i < n
      · rw [midFrom_of_lt R a b h, Bool.or_eq_true_iff, ih (i + 1) (by omega)]
        constructor
        · rintro (hb | ⟨m, hm, h1, h2⟩)
          · exact ⟨⟨i, h⟩, le_rfl, (Bool.and_eq_true_iff.1 hb).1, (Bool.and_eq_true_iff.1 hb).2⟩
          · exact ⟨m, by omega, h1, h2⟩
        · rintro ⟨m, hm, h1, h2⟩
          rcases Nat.eq_or_lt_of_le hm with hm' | hm'
          · refine Or.inl ?_
            have : (⟨i, h⟩ : Fin n) = m := Fin.ext hm'
            rw [this]
            simp [h1, h2]
          · exact Or.inr ⟨m, by omega, h1, h2⟩
      · rw [midFrom_of_ge R a b h]
        simp only [false_iff, Bool.false_eq_true, not_exists]
        rintro m ⟨hm, -, -⟩
        omega

