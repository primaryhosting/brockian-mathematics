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

-- Note: Lean 4 requires `import` lines to precede every other command, including module
-- doc comments, so the requested header comment appears verbatim immediately after the
-- single `import Mathlib` line.

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace Brockian.CullenWoodall

/-- The `n`-th Cullen number `C n = n * 2 ^ n + 1`. -/

theorem odd_prime_dvd_cullen_sub_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    p ∣ cullen (p - 2) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 ≤ p := by
    have h2 := hp.two_le
    rcases Nat.lt_or_ge p 3 with h3 | h3
    · interval_cases p <;> simp_all
    · exact h3
  refine (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).1 ?_
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have hdvd : p ∣ 2 := by
      have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
      exact (ZMod.natCast_zmod_eq_zero_iff_dvd 2 p).1 this
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have hferm : ((2 : ZMod p)) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one h2ne
  have hsub : ((p - 2 : ℕ) : ZMod p) = -2 := by
    have h2p : (2 : ℕ) ≤ p := by omega
    rw [Nat.cast_sub h2p, ZMod.natCast_self]
    push_cast
    ring
  simp only [cullen, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_one, Nat.cast_ofNat,
    hsub]
  have hpow : (2 : ZMod p) ^ (p - 2) * 2 = 2 ^ (p - 1) := by
    have hps : p - 1 = (p - 2) + 1 := by omega
    rw [hps, pow_succ]
  have hrw : (-2 : ZMod p) * 2 ^ (p - 2) = -(2 ^ (p - 2) * 2) := by ring
  rw [hrw, hpow, hferm]
  ring

/-- Every Cullen number `C (6k+2)` is divisible by `3`. -/
