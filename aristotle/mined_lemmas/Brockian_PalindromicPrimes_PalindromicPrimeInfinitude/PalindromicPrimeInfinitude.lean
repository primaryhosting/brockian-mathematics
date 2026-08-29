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

theorem PalindromicPrimeInfinitude :
    {p : ℕ | p.Prime ∧ IsPalindromic 10 p}.Infinite ↔
      ∀ k : ℕ, ∃ p : ℕ, p.Prime ∧ IsPalindromic 10 p ∧ k < (Nat.digits 10 p).length ∧
        Odd (Nat.digits 10 p).length := by
  constructor
  · intro hinf k
    obtain ⟨p, hpmem, hplt⟩ := hinf.exists_gt (10 ^ (k + 2))
    obtain ⟨hp, hpal⟩ := hpmem
    have hlen : k + 2 < (Nat.digits 10 p).length :=
      (Nat.lt_digits_length_iff (b := 10) (by norm_num) p).2 hplt.le
    have hne : p ≠ 11 := by
      rintro rfl
      norm_num at hlen
    exact ⟨p, hp, hpal, by omega, odd_length_of_palindromic_prime hp hpal hne⟩
  · intro h
    apply Set.infinite_of_forall_exists_gt
    intro a
    obtain ⟨p, hp, hpal, hlen, -⟩ := h a
    refine ⟨p, ⟨hp, hpal⟩, ?_⟩
    have hle : 10 ^ a ≤ p := (Nat.lt_digits_length_iff (b := 10) (by norm_num) p).1 hlen
    calc a < 10 ^ a := Nat.lt_pow_self (by norm_num)
      _ ≤ p := hle

end Brockian.PalindromicPrimes

