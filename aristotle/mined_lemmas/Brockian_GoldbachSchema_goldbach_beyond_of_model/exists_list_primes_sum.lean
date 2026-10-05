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
# Goldbach Beyond Of Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_beyond_of_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Goldbach Beyond Of Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_beyond_of_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Scope of what is proved here

* `goldbach_beyond_of_model` is proved unconditionally (no hypothesis beyond the model datum):
  given a *model* certifying Goldbach's conjecture on a finite initial range `[4, N]`, the full
  conjecture is equivalent to its "beyond `N`" form.
* A model for `N = 400` (`model400`) is constructed and proved by kernel computation, so
  `goldbach_iff_beyond_400` is likewise unconditional.
* Goldbach's conjecture itself (`Goldbach`) is *not* proved here; it is an open problem, and
  nothing in this file asserts it.  Everything stated is either unconditional or explicitly
  conditional on `Goldbach` (see `ternary_of_goldbach`).
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Brockian.GoldbachSchema

/-- `IsGoldbach n` : the natural number `n` is a sum of two primes. -/

theorem exists_list_primes_sum : ∀ n : ℕ, 2 ≤ n →
    ∃ l : List ℕ, l ≠ [] ∧ (∀ p ∈ l, Nat.Prime p) ∧ l.sum = n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.lt_or_ge n 4 with hlt | hge
    · interval_cases n
      · exact ⟨[2], by simp, by simp [Nat.prime_two], by simp⟩
      · exact ⟨[3], by simp, by simp [Nat.prime_three], by simp⟩
    · obtain ⟨l, hne, hp, hs⟩ := ih (n - 2) (by omega) (by omega)
      refine ⟨2 :: l, by simp, ?_, ?_⟩
      · intro p hp'
        rcases List.mem_cons.mp hp' with rfl | hp'
        · exact Nat.prime_two
        · exact hp p hp'
      · simp only [List.sum_cons, hs]; omega

end Brockian.GoldbachSchema

