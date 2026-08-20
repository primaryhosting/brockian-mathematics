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

theorem dvd_cullen_sub_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    p ∣ cullen (p - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h1 : 1 ≤ p := hp.one_lt.le
  have h2 : ((2 : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd)
  have hferm : ((2 : ℕ) : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one h2
  rw [← ZMod.natCast_eq_zero_iff]
  have hcast : ((cullen (p - 1) : ℕ) : ZMod p)
      = (((p : ℕ) : ZMod p) - 1) * ((2 : ℕ) : ZMod p) ^ (p - 1) + 1 := by
    simp only [cullen, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_one,
      Nat.cast_sub h1]
  rw [hcast, hferm, ZMod.natCast_self]
  ring

/-- For an odd prime `p`, the Cullen number `C (p - 1)` is strictly larger than `p`. -/
