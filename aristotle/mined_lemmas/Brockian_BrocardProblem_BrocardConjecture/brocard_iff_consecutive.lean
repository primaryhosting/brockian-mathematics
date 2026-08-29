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
# Brocard Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardProblem.BrocardConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to be the first command in a file, so the header above is a
-- plain block comment rather than a module docstring.)

import Mathlib

set_option maxRecDepth 40000

namespace Brockian.BrocardProblem

open Nat

/-- `IsBrocardSolution n m` says that `(n, m)` solves Brocard's equation `n! + 1 = m²`. -/

theorem brocard_iff_consecutive {n : ℕ} (hn : 2 ≤ n) :
    (∃ m : ℕ, IsBrocardSolution n m) ↔ ∃ a : ℕ, n ! = 4 * (a * (a + 1)) := by
  constructor
  · rintro ⟨m, hm⟩
    have hfac : 2 ∣ n ! := dvd_factorial (by norm_num) hn
    have hodd : ¬ (2 ∣ m) := by
      rintro ⟨t, rfl⟩
      obtain ⟨s, hs⟩ := hfac
      unfold IsBrocardSolution at hm
      have h4 : (2 * t) ^ 2 = 4 * (t * t) := by ring
      omega
    obtain ⟨a, ha⟩ : ∃ a, m = 2 * a + 1 := by
      rcases Nat.even_or_odd m with h | h
      · exact absurd h.two_dvd hodd
      · obtain ⟨a, ha⟩ := h; exact ⟨a, by omega⟩
    refine ⟨a, ?_⟩
    unfold IsBrocardSolution at hm
    subst ha
    nlinarith [hm]
  · rintro ⟨a, ha⟩
    exact ⟨2 * a + 1, by unfold IsBrocardSolution; rw [ha]; ring⟩

/-- Any solution of Brocard's equation produces two consecutive integers all of whose
prime factors are at most `n` (i.e. two consecutive `n`-smooth numbers). -/
