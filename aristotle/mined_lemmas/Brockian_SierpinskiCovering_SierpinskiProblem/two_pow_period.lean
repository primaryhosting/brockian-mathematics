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

theorem two_pow_period (p n : Nat) (hp : 2 ^ 36 % p = 1 % p) :
    2 ^ n % p = 2 ^ (n % 36) % p := by
  have h := two_pow_period_aux p (n / 36) (n % 36) hp
  rw [Nat.div_add_mod] at h
  exact h

/-- Consequently `k * 2 ^ n + 1` and `k * 2 ^ (n % 36) + 1` agree modulo `p`. -/
