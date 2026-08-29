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
# Palindromic Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.PalindromicPrimes.PalindromicPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.PalindromicPrimes

/-- `IsPalindrome b n` says that the base-`b` digit expansion of `n` reads the same
forwards and backwards. -/

lemma le_digits_length_of_pow_le {N n : ℕ} (h : 10 ^ N ≤ n) : N ≤ (Nat.digits 10 n).length := by
  have hn : n ≠ 0 := by
    rintro rfl
    exact absurd h (by positivity : (0:ℕ) < 10 ^ N).not_ge
  rw [Nat.digits_len 10 n (by norm_num) hn]
  exact le_trans ((Nat.le_log_iff_pow_le (by norm_num) hn).2 h) (Nat.le_succ _)

/-! ### Even-length palindromes are divisible by 11 -/

/-- A palindromic list of even length has vanishing alternating sum. -/
