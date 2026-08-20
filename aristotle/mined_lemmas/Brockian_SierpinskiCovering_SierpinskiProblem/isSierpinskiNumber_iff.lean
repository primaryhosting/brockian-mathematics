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

theorem isSierpinskiNumber_iff (k : ℕ) :
    IsSierpinskiNumber k ↔
      Odd k ∧ 0 < k ∧ ∀ n : ℕ, 1 ≤ n → ¬ Nat.Prime (k * 2 ^ n + 1) := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨Nat.odd_iff.mpr h1, h2, fun n hn => (h3 n hn).not_prime⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨Nat.odd_iff.mp h1, h2, fun n hn => ?_⟩
    have hN : 2 ≤ k * 2 ^ n + 1 := by
      have : 1 * 2 ^ 1 ≤ k * 2 ^ n :=
        Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by norm_num) hn)
      omega
    obtain ⟨d, hd, hdvd⟩ := Nat.exists_prime_and_dvd (n := k * 2 ^ n + 1) (by omega)
    refine ⟨d, hdvd, hd.one_lt, ?_⟩
    rcases (Nat.le_of_dvd (by omega) hdvd).lt_or_eq with h | h
    · exact h
    · exact absurd (h ▸ hd) (h3 n hn)

/-- `78557 * 2 ^ n + 1` is never prime: `78557` is a Sierpiński number. -/
