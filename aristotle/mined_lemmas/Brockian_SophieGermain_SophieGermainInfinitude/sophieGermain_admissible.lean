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

/-- `p` is a Sophie Germain prime: both `p` and `2 * p + 1` are prime. -/

theorem sophieGermain_admissible (q : ℕ) (hq : q.Prime) :
    ∃ n : ℤ, ¬ ((q : ℤ) ∣ ∏ i, ((![0, 1] : Fin 2 → ℤ) i + (![1, 2] : Fin 2 → ℤ) i * n)) := by
  refine ⟨-1, ?_⟩
  rw [Fin.prod_univ_two]
  norm_num
  intro h
  have : q ∣ 1 := by exact_mod_cast h
  exact hq.one_lt.ne' (Nat.dvd_one.mp this)

/-- **Conditional reduction.** Dickson's conjecture implies that there are infinitely many
Sophie Germain primes. -/
