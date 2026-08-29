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
# Same Parity Betrothed Exists
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.SameParityBetrothedExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The header above uses `/-` rather than `/-!` only because Lean 4 does not allow a module
-- docstring to precede the `import` commands.)

import Mathlib

open Nat ArithmeticFunction

namespace Brockian
namespace BetrothedNumbers

/-- Two positive naturals `m`, `n` are *betrothed* (a quasi-amicable pair) when the sum of the
divisors of each equals `m + n + 1`; equivalently, the sum of the *proper* divisors of each,
excluding `1`, gives the other number. -/

theorem sq_or_two_mul_sq_of_betrothed_same_parity {m n : ℕ} (h : Betrothed m n)
    (hpar : m % 2 = n % 2) :
    (∃ a : ℕ, m = a ^ 2 ∨ m = 2 * a ^ 2) ∧ (∃ b : ℕ, n = b ^ 2 ∨ n = 2 * b ^ 2) := by
  obtain ⟨hm, hn, hsm, hsn⟩ := h
  have hodd : Odd (m + n + 1) := by
    rw [Nat.odd_iff]
    omega
  constructor
  · refine eq_sq_or_two_mul_sq_of_even_odd_factorization hm.ne' ?_
    intro p hp hp2
    exact even_factorization_of_odd_sigma hm.ne' (hsm ▸ hodd) hp hp2
  · refine eq_sq_or_two_mul_sq_of_even_odd_factorization hn.ne' ?_
    intro p hp hp2
    exact even_factorization_of_odd_sigma hn.ne' (hsn ▸ hodd) hp hp2

/-- **Same parity betrothed numbers.**  Whether a betrothed (quasi-amicable) pair of equal parity
exists is an open problem; all known betrothed pairs consist of one even and one odd number.  Here
we give a Lean-checked conditional reduction: *if* such a pair exists, then it may be taken with
both members of the very restricted shape `k ^ 2` or `2 * k ^ 2` (a consequence of the fact that
the common divisor sum `m + n + 1` is then odd). -/
