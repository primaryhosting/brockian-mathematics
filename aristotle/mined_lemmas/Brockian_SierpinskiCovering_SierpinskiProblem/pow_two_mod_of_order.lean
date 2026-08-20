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
import Brockian.SierpinskiCovering

/-!
# Sierpiński numbers: Mathlib-flavoured restatement

`Brockian/SierpinskiCovering.lean` must be import-free (its mandated header comment has to
precede everything, and Lean requires `import` to come first), so it develops the covering
argument using only the core `Nat` API.  Here we restate its conclusions with the usual
Mathlib vocabulary: `Nat.Prime`, `Odd`, and `Set.Infinite`.
-/

namespace Brockian.SierpinskiCovering

/-- A composite number is not prime. -/

theorem pow_two_mod_of_order {p n : Nat} (h : 2 ^ 36 % p = 1 % p) :
    2 ^ n % p = 2 ^ (n % 36) % p := by
  have hsplit : n = 36 * (n / 36) + n % 36 := by omega
  calc 2 ^ n % p
      = ((2 ^ 36) ^ (n / 36) * 2 ^ (n % 36)) % p := by
        rw [← Nat.pow_mul, ← Nat.pow_add, ← hsplit]
    _ = (((2 ^ 36) ^ (n / 36)) % p * (2 ^ (n % 36) % p)) % p := by rw [Nat.mul_mod]
    _ = ((1 ^ (n / 36)) % p * (2 ^ (n % 36) % p)) % p := by
        rw [Nat.pow_mod, h, ← Nat.pow_mod]
    _ = 2 ^ (n % 36) % p := by rw [Nat.one_pow, ← Nat.mul_mod, Nat.one_mul]

/-- **The covering argument.** For every `k` congruent to `78557` modulo `70050435` and every
`n`, the number `k * 2 ^ n + 1` is divisible by the covering prime attached to `n % 36`. -/
