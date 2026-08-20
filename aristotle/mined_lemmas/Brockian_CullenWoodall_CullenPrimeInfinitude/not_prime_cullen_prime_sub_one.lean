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
# Cullen Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.CullenPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on file layout: Lean 4 requires all `import` commands to appear before any
other command, including module docstrings, so the mandated header comment above
is placed immediately after the single `import Mathlib` line.
-/

namespace Brockian.CullenWoodall

/-- The `n`-th **Cullen number** `C n = n * 2 ^ n + 1`. -/

theorem not_prime_cullen_prime_sub_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ Nat.Prime (cullen (p - 1)) := by
  intro hprime
  have hdvd := dvd_cullen_sub_one hp hp2
  have heq := (Nat.prime_dvd_prime_iff_eq hp hprime).mp hdvd
  exact absurd heq (Nat.ne_of_lt (lt_cullen_sub_one hp hp2))

/-- **Unconditional partial result.** There are infinitely many `n` for which the
Cullen number `n * 2 ^ n + 1` is *not* prime. -/
