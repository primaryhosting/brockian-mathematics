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

-- (The header above uses `/-` rather than `/-!` because Lean 4 does not permit a module
-- docstring to precede the `import` block; the text is otherwise verbatim.)

import Mathlib

/-!
# Three Prime Carmichael Infinitude
Category: Brockian Conjecture
Target: Brockian.CarmichaelKorselt.ThreePrimeCarmichaelInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.CarmichaelKorselt

/-- `n` is a Carmichael number: it is composite, yet `a ^ n ≡ a [ZMOD n]` for every integer `a`. -/

theorem prime_dvd_pow_sub_self {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n)
    (hd : (p - 1) ∣ (n - 1)) (a : ℤ) : (p : ℤ) ∣ a ^ n - a := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨t, ht⟩ := hd
  have hn' : n = (p - 1) * t + 1 := by omega
  have key : ((a : ZMod p)) ^ n = (a : ZMod p) := by
    by_cases h0 : (a : ZMod p) = 0
    · rw [h0, zero_pow (by omega)]
    · rw [hn', pow_add, pow_one, pow_mul, ZMod.pow_card_sub_one_eq_one h0, one_pow, one_mul]
  have hzero : ((a ^ n - a : ℤ) : ZMod p) = 0 := by push_cast; rw [key]; ring
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hzero

/-- Korselt's criterion (sufficiency) for a product of three distinct primes. -/
