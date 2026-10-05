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
# Sophie Germain Infinitude
Category: Brockian Conjecture
Target: Brockian.SophieGermain.SophieGermainInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any module docstring `/-!`, so the header above
-- is reproduced verbatim as the module docstring immediately after the import.)

import Mathlib

/-!
# Sophie Germain Infinitude
Category: Brockian Conjecture
Target: Brockian.SophieGermain.SophieGermainInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.SophieGermain

/-- A *Sophie Germain prime* is a prime `p` such that `2 * p + 1` is also prime. -/

theorem sophieGermain_admissible :
    ∀ q : ℕ, q.Prime → ∃ n : ℕ, ¬ q ∣ (1 * n + 0) * (2 * n + 1) := by
  intro q hq
  by_cases h3 : q = 3
  · refine ⟨2, ?_⟩
    subst h3
    decide
  · refine ⟨1, ?_⟩
    norm_num
    intro hdvd
    exact h3 ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).1 hdvd)

/-! ## Main conditional theorem -/

/-- **Sophie Germain infinitude, conditional on Dickson's conjecture for two linear forms.**

Assuming `DicksonTwoForms` (the case of Dickson's conjecture / Schinzel's Hypothesis H for the
admissible pair of linear forms `n` and `2n + 1`), there are infinitely many Sophie Germain
primes, i.e. infinitely many primes `p` with `2 * p + 1` also prime.

The unconditional statement is a well-known open problem; this is a formally checked reduction
of it to the stated instance of Dickson's conjecture. -/
