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

theorem eq_one_or_two_of_squarefree {a : ℕ} (hsq : Squarefree a)
    (h : ∀ p : ℕ, p.Prime → p ∣ a → p = 2) : a = 1 ∨ a = 2 := by
  have ha0 : a ≠ 0 := hsq.ne_zero
  rcases eq_or_ne a 1 with rfl | h1
  · exact Or.inl rfl
  · obtain ⟨p, hp, hpa⟩ := Nat.exists_prime_and_dvd h1
    have hp2 : p = 2 := h p hp hpa
    subst hp2
    have hle : a.factorization 2 ≤ 1 := by
      by_contra hc
      have h4 : (2 : ℕ) ^ 2 ∣ a :=
        (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two ha0).mpr (by omega)
      exact Nat.prime_two.not_isUnit (hsq 2 (by simpa [pow_two] using h4))
    have hge : 1 ≤ a.factorization 2 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two ha0).mp (by simpa using hpa)
    have heq : a = 2 ^ a.primeFactorsList.length :=
      Nat.eq_prime_pow_of_unique_prime_dvd ha0 (fun {d} hd hda => h d hd hda)
    -- the exponent is exactly `a.factorization 2`
    have hlen : a.primeFactorsList.length = a.factorization 2 := by
      conv_rhs => rw [heq]
      simp [Nat.prime_two.factorization]
    rw [hlen] at heq
    right
    rw [heq]
    have : a.factorization 2 = 1 := le_antisymm hle hge
    rw [this, pow_one]

/-- A positive number all of whose odd primes occur to an even power is a square or twice a
square. -/
