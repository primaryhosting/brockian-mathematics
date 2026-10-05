import Brockian.OreHarmonicNumbers
import Brockian.OreHarmonicNumbersTheory

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

/-!
# Odd Harmonic Exists
Category: Brockian Conjecture
Target: Brockian.OreHarmonicNumbers.OddHarmonicExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
## Ore harmonic (harmonic divisor) numbers

A positive integer `n` is an *Ore harmonic number* (a harmonic divisor number) when the
harmonic mean of its divisors,

  `H(n) = n * τ(n) / σ(n)`,

is an integer, i.e. when `σ(n) ∣ n * τ(n)`, where `τ(n)` is the number of divisors of `n`
and `σ(n)` is their sum.

The target `OddHarmonicExists` asserts that an *odd* Ore harmonic number exists; it is
witnessed by `n = 1`, for which `H(1) = 1`.

Ore's conjecture — that `1` is the *only* odd harmonic number — is a well-known open problem.
It is recorded (as a `Prop`, not asserted) in the companion file
`Brockian/OreHarmonicNumbersTheory.lean`, together with unconditional partial results towards
it and the identification of the definitions below with Mathlib's `σ` and `τ`.

This file is deliberately import-free (plain core Lean), since the required header comment must
be the very first thing in the file and Lean does not allow a module doc comment before
`import` commands.
-/

namespace Brockian.OreHarmonicNumbers

/-- The list of (positive) divisors of `n`, in increasing order. For `n = 0` this is `[]`. -/

theorem one_lt_card_primeFactors_of_isOreHarmonic {n : ℕ} (hn : 1 < n)
    (h : IsOreHarmonic n) : 1 < n.primeFactors.card := by
  rcases Nat.lt_or_ge n.primeFactors.card 2 with hcard | hcard
  · interval_cases hc : n.primeFactors.card
    · exact absurd (Nat.primeFactors_eq_empty.mp (Finset.card_eq_zero.mp hc)) (by omega)
    · obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hc
      have hpp : p.Prime :=
        Nat.prime_of_mem_primeFactors (by rw [hp]; exact Finset.mem_singleton_self p)
      have hne : n ≠ 0 := by omega
      have hfac : n = p ^ n.factorization p := by
        conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hne]
        rw [Nat.prod_factorization_eq_prod_primeFactors, hp]
        simp
      have hk : 1 ≤ n.factorization p := by
        rcases Nat.eq_zero_or_pos (n.factorization p) with h0 | h0
        · rw [h0, pow_zero] at hfac; omega
        · omega
      exact absurd (hfac ▸ h) (not_isOreHarmonic_prime_pow hpp hk)
  · omega

/-! ### Ore's conjecture -/

/-- **Ore's conjecture** (open): `1` is the only odd Ore harmonic number. -/
