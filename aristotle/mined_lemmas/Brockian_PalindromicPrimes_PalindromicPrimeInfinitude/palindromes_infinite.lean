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
# Palindromic Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.PalindromicPrimes.PalindromicPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 requires `import` commands to precede every other command, including
module docstrings, so the header above is a plain block comment `/- ... -/`; the same
text is repeated as the module docstring `/-! ... -/` immediately after the import.)
-/

import Mathlib

/-!
# Palindromic Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.PalindromicPrimes.PalindromicPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.PalindromicPrimes

open Nat

/-- `IsPalindromic b n` says that the base-`b` digit expansion of `n` reads the same
forwards and backwards. -/

theorem palindromes_infinite : {n : ℕ | IsPalindromic 10 n}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  have hd : Nat.digits 10 (Nat.ofDigits 10 (padList a)) = padList a :=
    Nat.digits_ofDigits 10 (by norm_num) _ (padList_lt a) (padList_getLast a)
  refine ⟨Nat.ofDigits 10 (padList a), ?_, ?_⟩
  · show IsPalindromic 10 _
    rw [IsPalindromic, hd, padList_reverse]
  · have hlen : a < (Nat.digits 10 (Nat.ofDigits 10 (padList a))).length := by
      rw [hd, padList_length]; omega
    have hle := (Nat.lt_digits_length_iff (b := 10) (by norm_num)
      (Nat.ofDigits 10 (padList a))).1 hlen
    calc a < 10 ^ a := Nat.lt_pow_self (by norm_num)
      _ ≤ _ := hle

/-- Every base-10 palindrome with an even number of digits is divisible by `11`. -/
