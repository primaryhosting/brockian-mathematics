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

theorem tau_lt_sigmaOne_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    tau (p ^ k) < sigmaOne (p ^ k) := by
  rw [tau_prime_pow hp, sigmaOne_prime_pow hp]
  have key : ∑ _i ∈ range (k + 1), 1 < ∑ i ∈ range (k + 1), p ^ i := by
    refine Finset.sum_lt_sum (fun i _ => Nat.one_le_pow _ _ hp.pos) ⟨1, ?_, ?_⟩
    · simp only [Finset.mem_range]; omega
    · simpa using hp.one_lt
  simpa using key

/-! ### No prime power `> 1` is harmonic -/

/-- No prime power `p ^ k` with `k ≥ 1` is an Ore harmonic number. -/
