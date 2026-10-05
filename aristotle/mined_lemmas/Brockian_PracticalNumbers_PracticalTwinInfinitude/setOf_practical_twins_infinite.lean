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

import Mathlib

/-!
# Practical Twin Infinitude
Category: Brockian Conjecture
Target: Brockian.PracticalNumbers.PracticalTwinInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.PracticalNumbers

/-- A natural number `n` is *practical* if it is positive and every `t ≤ n` can be written
as a sum of distinct divisors of `n`. -/

theorem setOf_practical_twins_infinite :
    {n : ℕ | Practical n ∧ Practical (n + 2)}.Infinite := by
  refine Set.infinite_of_forall_exists_gt ?_
  intro M
  obtain ⟨n, hn, h1, h2⟩ := PracticalTwinInfinitude M
  exact ⟨n, ⟨h1, h2⟩, hn⟩

/-- Sanity check: the notion of practicality is not vacuous; `5` is not practical. -/
example : ¬ Practical 5 := by
  rintro ⟨-, h⟩
  obtain ⟨S, hS, hsum⟩ := h 4 (by norm_num)
  have hd : (5:ℕ).divisors = {1, 5} := by decide
  rw [hd] at hS
  have hmem : S ∈ ({1, 5} : Finset ℕ).powerset := Finset.mem_powerset.mpr hS
  fin_cases hmem <;> simp_all

end Brockian.PracticalNumbers

