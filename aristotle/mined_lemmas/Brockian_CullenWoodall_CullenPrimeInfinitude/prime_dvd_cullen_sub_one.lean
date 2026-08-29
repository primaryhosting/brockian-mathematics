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
# Cullen Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.CullenPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede every command, including module
-- docstrings, so the header above is a plain block comment and is repeated as a
-- module docstring after the import.)

import Mathlib

/-!
# Cullen Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.CullenPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Brockian.CullenWoodall

/-- The `n`-th Cullen number `C n = n * 2 ^ n + 1`. -/

theorem prime_dvd_cullen_sub_one (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2) :
    p ∣ cullen (p - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp1 : 1 ≤ p := hp.one_lt.le
  have hcast : ((p - 1 : ℕ) : ZMod p) = -1 := by
    have : ((p - 1 : ℕ) : ZMod p) = (p : ZMod p) - 1 := by
      push_cast [Nat.cast_sub hp1]; ring
    rw [this, ZMod.natCast_self]; ring
  have : ((cullen (p - 1) : ℕ) : ZMod p) = 0 := by
    unfold cullen
    push_cast
    rw [hcast, two_pow_sub_one_eq_one p hp hodd]
    ring
  exact (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp this

/-- For a prime `p ≥ 5` the Cullen number `C (p - 1)` is composite. -/
