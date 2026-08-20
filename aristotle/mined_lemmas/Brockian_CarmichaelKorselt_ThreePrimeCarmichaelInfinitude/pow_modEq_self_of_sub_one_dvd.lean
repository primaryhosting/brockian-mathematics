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
# Three Prime Carmichael Infinitude
Category: Brockian Conjecture
Target: Brockian.CarmichaelKorselt.ThreePrimeCarmichaelInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian
namespace CarmichaelKorselt

/-- A *Carmichael number*: a composite `n > 1` which is a Fermat pseudoprime to every base,
i.e. `a ^ n ≡ a [MOD n]` for all `a`. -/

theorem pow_modEq_self_of_sub_one_dvd {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n)
    (hdvd : p - 1 ∣ n - 1) (a : ℕ) : a ^ n ≡ a [MOD p] := by
  haveI : Fact p.Prime := ⟨hp⟩
  have key : ((a : ZMod p)) ^ n = (a : ZMod p) := by
    obtain ⟨c, hc⟩ := hdvd
    have hn' : n = (p - 1) * c + 1 := by omega
    rcases eq_or_ne (a : ZMod p) 0 with h0 | h0
    · rw [h0, zero_pow (by omega)]
    · rw [hn', pow_succ, pow_mul, ZMod.pow_card_sub_one_eq_one h0, one_pow, one_mul]
  exact (ZMod.natCast_eq_natCast_iff (a ^ n) a p).mp (by push_cast; exact key)

/-- Korselt's criterion (sufficiency) for a product of three distinct primes. -/
