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
# Quasiperfect Exists
Category: Brockian Conjecture
Target: Brockian.QuasiperfectNumbers.QuasiperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.QuasiperfectNumbers

open Finset

/-- A natural number `n` is *quasiperfect* if the sum of its divisors equals `2 * n + 1`,
i.e. the sum of its proper divisors is `n + 1`. -/

lemma not_dvd_sq_add_one {p t : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3) : ¬ p ∣ t ^ 2 + 1 := by
  intro hdvd
  haveI : Fact p.Prime := ⟨hp⟩
  have h0 : ((t ^ 2 + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).mpr hdvd
  push_cast at h0
  have hsq : IsSquare (-1 : ZMod p) := ⟨(t : ZMod p), by linear_combination -h0⟩
  exact (ZMod.exists_sq_eq_neg_one_iff.mp hsq) hp4

/-- If `n` has an odd number of divisors, then `n` is a perfect square. -/
