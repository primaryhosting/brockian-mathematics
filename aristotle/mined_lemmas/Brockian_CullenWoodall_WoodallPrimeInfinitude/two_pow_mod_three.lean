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
# Woodall Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.WoodallPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Woodall Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.WoodallPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.CullenWoodall

/-- The `n`-th Woodall number `W n = n * 2 ^ n - 1` (natural subtraction; harmless
since `n * 2 ^ n ≥ 1` for `n ≥ 1`). -/

lemma two_pow_mod_three (n : ℕ) : 2 ^ n % 3 = if n % 2 = 0 then 1 else 2 := by
  induction n with
  | zero => rfl
  | succ k ih =>
      have hstep : 2 ^ (k + 1) % 3 = (2 * (2 ^ k % 3)) % 3 := by
        rw [pow_succ]
        omega
      rw [hstep, ih]
      rcases Nat.even_or_odd k with hk | hk
      · have h0 : k % 2 = 0 := Nat.even_iff.1 hk
        rw [if_pos h0, if_neg (by omega)]
      · have h1 : k % 2 = 1 := Nat.odd_iff.1 hk
        rw [if_neg (by omega), if_pos (by omega)]

/-- If `n ≡ 4` or `n ≡ 5 (mod 6)` then `3 ∣ W n`. -/
