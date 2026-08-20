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
# Woodall Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.WoodallPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Woodall Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.WoodallPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.CullenWoodall

/-- The `n`-th Woodall number `W n = n * 2 ^ n - 1` (natural subtraction; harmless
since `n * 2 ^ n ≥ 1` for `n ≥ 1`). -/

theorem woodall_not_prime_of_mod_six {n : ℕ} (hn : n % 6 = 4 ∨ n % 6 = 5) :
    ¬ (woodall n).Prime := by
  intro hp
  have hdvd : 3 ∣ woodall n := three_dvd_woodall hn
  have hle : n ≤ woodall n := le_woodall (by omega)
  have hlt : 3 < woodall n := by omega
  rcases hp.eq_one_or_self_of_dvd 3 hdvd with h | h <;> omega

/-- There are infinitely many composite Woodall numbers. -/
