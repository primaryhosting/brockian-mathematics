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
# Three Prime Carmichael Infinitude
Category: Brockian Conjecture
Target: Brockian.CarmichaelKorselt.ThreePrimeCarmichaelInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Three Prime Carmichael Infinitude
Category: Brockian Conjecture
Target: Brockian.CarmichaelKorselt.ThreePrimeCarmichaelInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian
namespace CarmichaelKorselt

/-- A *Carmichael number*: a composite `n > 1` which is a Fermat pseudoprime to every base,
i.e. `n ∣ a ^ n - a` for all integers `a`. -/

theorem prime_dvd_pow_sub_self {p n t : ℕ} (hp : p.Prime) (hn : n = 1 + (p - 1) * t) (a : ℤ) :
    (p : ℤ) ∣ a ^ n - a := by
  haveI := Fact.mk hp
  have key : ((a ^ n - a : ℤ) : ZMod p) = 0 := by
    push_cast
    subst hn
    set b : ZMod p := (a : ZMod p) with hb
    rcases eq_or_ne b 0 with h | h
    · simp [h, pow_add]
    · rw [pow_add, pow_one, pow_mul, ZMod.pow_card_sub_one_eq_one h, one_pow, mul_one, sub_self]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp key

/-- The expansion `(6k+1)(12k+1)(18k+1) = 1 + 36k(36k² + 11k + 1)`. -/
