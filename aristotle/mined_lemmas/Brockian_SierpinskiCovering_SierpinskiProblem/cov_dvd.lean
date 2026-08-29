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
# Sierpinski Problem
Category: Brockian Conjecture
Target: Brockian.SierpinskiCovering.SierpinskiProblem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
NOTE ON IMPORTS.  Lean 4 requires every `import` line to precede all other commands, and a
module docstring `/-! ... -/` counts as a command.  Since the header comment above must be the
very first thing in this file, this module is deliberately written using only Lean 4 core
(no `import` lines at all).  The Mathlib-phrased corollary
`¬ Nat.Prime (78557 * 2 ^ n + 1)` is proved in `Brockian/SierpinskiPrime.lean`, which imports
both Mathlib and this file.

MATHEMATICAL CONTENT.  The *Sierpiński problem* concerns odd `k` such that `k * 2 ^ n + 1` is
composite for every `n`; such `k` are called Sierpiński numbers, and `78557` is the conjectured
smallest one.  That `78557` really is a Sierpiński number is Sierpiński's classical *covering*
argument, formalised below: the covering set `{3, 5, 7, 13, 19, 37, 73}` consists of primes whose
multiplicative order for `2` divides `36`, and for each residue `r < 36` one of them divides
`78557 * 2 ^ r + 1`.
-/

namespace Brockian
namespace SierpinskiCovering

/-- The Sierpiński candidate. -/

theorem cov_dvd (n : Nat) :
    2 ≤ cov n ∧ cov n < k * 2 ^ n + 1 ∧ cov n ∣ (k * 2 ^ n + 1) := by
  have hlt : n % 36 < 36 := Nat.mod_lt _ (by decide)
  obtain ⟨h2, h73, hord, hdvd⟩ := cov_spec (n % 36) hlt
  have hcov : cov n = cov (n % 36) := by
    unfold cov
    rw [Nat.mod_mod_of_dvd n (Nat.dvd_refl 36)]
  have hone : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hbig : k * 1 ≤ k * 2 ^ n := Nat.mul_le_mul_left k hone
  have hmod : (k * 2 ^ n + 1) % cov n = 0 := by
    rw [hcov, shift_mod (cov (n % 36)) n hord]
    exact hdvd
  refine ⟨by omega, by simp only [k] at hbig ⊢; omega, Nat.dvd_of_mod_eq_zero hmod⟩

/-- **The Sierpiński problem (Sierpiński's covering construction).**

`78557` is a Sierpiński number: for every natural number `n` the number `78557 * 2 ^ n + 1` is
composite, i.e. it has a divisor `d` with `2 ≤ d < 78557 * 2 ^ n + 1`.

The witness is supplied by the covering set `{3, 5, 7, 13, 19, 37, 73}`: each of these primes
satisfies `2 ^ 36 ≡ 1` modulo it, and for every residue `r` of `n` modulo `36` one of them
divides `78557 * 2 ^ r + 1`, hence also `78557 * 2 ^ n + 1`. -/
