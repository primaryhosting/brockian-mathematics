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
# Quasiperfect Exists
Category: Brockian Conjecture
Target: Brockian.QuasiperfectNumbers.QuasiperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean requires `import` commands to precede every other command, including
module doc comments, so the header above is a plain comment and is repeated as the
module docstring after the import below.)
-/

import Mathlib

/-!
# Quasiperfect Exists
Category: Brockian Conjecture
Target: Brockian.QuasiperfectNumbers.QuasiperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian
namespace QuasiperfectNumbers

open Finset

/-- A natural number `n` is *quasiperfect* if the sum of all its divisors equals `2 * n + 1`,
i.e. `σ n = 2n + 1`.  Whether a quasiperfect number exists is an open problem. -/

theorem not_dvd_sq_add_one_of_three_mod_four {D k : ℕ} (hD : D % 4 = 3) :
    ¬ D ∣ k ^ 2 + 1 := by
  intro hdvd
  obtain ⟨p, hp, hp3, hpd⟩ := exists_prime_three_mod_four_dvd D hD
  have hpk : p ∣ k ^ 2 + 1 := hpd.trans hdvd
  haveI : Fact p.Prime := ⟨hp⟩
  have hz : ((k : ZMod p)) ^ 2 + 1 = 0 := by
    have h2 : ((k ^ 2 + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).mpr hpk
    push_cast at h2
    exact h2
  have hsq : IsSquare (-1 : ZMod p) := ⟨(k : ZMod p), by linear_combination -hz⟩
  exact (ZMod.exists_sq_eq_neg_one_iff.mp hsq) hp3

/-- Every divisor of an odd number is odd. -/
