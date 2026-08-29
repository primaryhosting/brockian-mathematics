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

lemma fermatNumber_mod_four (n : ℕ) (hn : 1 ≤ n) : Nat.fermatNumber n % 4 = 1 := by
  have h2 : 2 ≤ 2 ^ n := by
    calc (2 : ℕ) = 2 ^ 1 := rfl
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h : (2 : ℕ) ^ 2 ^ n = 4 * 2 ^ (2 ^ n - 2) := by
    rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_add]
    congr 1
    omega
  simp [Nat.fermatNumber, h, Nat.add_mod, Nat.mul_mod_right]

/-- `Fₙ ≡ 2 [MOD 3]` for `n ≥ 1`. -/
