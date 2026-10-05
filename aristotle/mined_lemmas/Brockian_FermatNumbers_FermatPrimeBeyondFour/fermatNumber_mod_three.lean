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
# Fermat Prime Beyond Four
Category: Brockian Conjecture
Target: Brockian.FermatNumbers.FermatPrimeBeyondFour
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.FermatNumbers

private instance factPrimeThree : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- The Pépin condition for the `n`-th Fermat number `Fₙ = 2 ^ 2 ^ n + 1`:
`3 ^ ((Fₙ - 1) / 2) = -1` in `ZMod Fₙ`. -/

lemma fermatNumber_mod_three (n : ℕ) (hn : 1 ≤ n) : Nat.fermatNumber n % 3 = 2 := by
  obtain ⟨k, hk⟩ : ∃ k, 2 ^ n = 2 * k := ⟨2 ^ (n - 1), by
    rw [show (2 : ℕ) * 2 ^ (n - 1) = 2 ^ (n - 1 + 1) by ring]
    congr 1
    omega⟩
  have h : (2 : ℕ) ^ 2 ^ n % 3 = 1 := by
    rw [hk, pow_mul, show (2 : ℕ) ^ 2 = 3 + 1 by norm_num]
    simpa using Nat.pow_mod (3 + 1) k 3
  simp [Nat.fermatNumber, Nat.add_mod, h]

/-- `3` is a quadratic non-residue modulo a prime Fermat number `Fₙ` with `n ≥ 1`. -/
