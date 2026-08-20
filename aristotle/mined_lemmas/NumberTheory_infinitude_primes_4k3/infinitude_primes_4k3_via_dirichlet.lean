import Mathlib

/-!
# Infinitude Primes 4 K 3
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.infinitude_primes_4k3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace NumberTheory

/-- Every natural number congruent to `3` modulo `4` has a prime divisor that is itself
congruent to `3` modulo `4`.

Indeed such a number is odd, so all of its prime factors are odd; if all of them were
congruent to `1` modulo `4`, so would be their product. -/

theorem infinitude_primes_4k3_via_dirichlet (N : ℕ) :
    ∃ p : ℕ, p.Prime ∧ N < p ∧ p % 4 = 3 := by
  obtain ⟨p, hpN, hp, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq N (q := 4) (a := 3) (by norm_num) (by decide)
  exact ⟨p, hp, hpN, by simpa [Nat.ModEq] using hmod⟩

end NumberTheory

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

