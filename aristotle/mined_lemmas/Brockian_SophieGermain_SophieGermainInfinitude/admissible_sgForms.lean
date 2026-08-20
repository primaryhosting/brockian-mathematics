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
# Sophie Germain Infinitude
Category: Brockian Conjecture
Target: Brockian.SophieGermain.SophieGermainInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.SophieGermain

/-- `p` is a *Sophie Germain prime* if both `p` and `2 * p + 1` are prime. -/

theorem admissible_sgForms : Admissible sgForms := by
  intro q hq
  by_cases h3 : q = 3
  · subst h3
    refine ⟨2, ?_⟩
    intro i
    fin_cases i <;> simp [sgForms]
  · refine ⟨1, ?_⟩
    intro i
    fin_cases i <;> simp [sgForms]
    · exact hq.one_lt.ne'
    · intro hdvd
      exact h3 ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp hdvd)

/-! ## The conditional reduction -/

/-- **Sophie Germain infinitude, conditional on Dickson's conjecture.**

Assuming Dickson's conjecture for admissible families of linear forms, there are infinitely
many Sophie Germain primes, i.e. infinitely many primes `p` with `2 * p + 1` also prime.

(The unconditional statement is a well-known open problem; this is a Lean-checked reduction.) -/
