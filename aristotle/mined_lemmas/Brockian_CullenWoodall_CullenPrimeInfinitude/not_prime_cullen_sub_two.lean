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

(The header comment is placed immediately after `import Mathlib` because Lean 4
requires `import` commands to precede every other command, including module
docstrings; the header text itself is verbatim.)
-/

set_option maxHeartbeats 1000000

namespace Brockian.CullenWoodall

/-- The `n`-th Cullen number `C n = n * 2 ^ n + 1`. -/

theorem not_prime_cullen_sub_two {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ¬ (cullen (p - 2)).Prime := by
  intro hprime
  have hdvd : p ∣ cullen (p - 2) := prime_dvd_cullen_sub_two hp (by omega)
  have hlt : (p - 2) + 2 < cullen (p - 2) := lt_cullen_of_two_le (by omega)
  rcases hprime.eq_one_or_self_of_dvd p hdvd with h | h
  · omega
  · omega

/-- There are infinitely many composite Cullen numbers. -/
