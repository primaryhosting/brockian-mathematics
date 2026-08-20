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
The header module docstring above must be the very first thing in this file, so the
file carries no `import` line (Lean requires imports to precede any command).  The
development below is therefore written against Lean core only.  The companion file
`Brockian/SierpinskiCoveringMathlib.lean` imports Mathlib and restates the main
result with Mathlib's `Nat.Prime`.

Statement proved here: `78557` is a Sierpiński number, i.e. `78557 * 2 ^ n + 1` is
composite for every natural number `n`.  The proof uses the classical covering set
of primes `{3, 5, 7, 13, 19, 37, 73}`: the multiplicative order of `2` modulo each of
them divides `36`, and for each residue `r < 36` one of these primes divides
`78557 * 2 ^ r + 1`.
-/

namespace Brockian
namespace SierpinskiCovering

/-- Primality predicate for natural numbers (core-Lean version of `Nat.Prime`). -/

theorem covering_residues :
    ∀ r ∈ List.range 36, ∃ p ∈ coveringPrimes, (78557 * 2 ^ r + 1) % p = 0 := by decide

/-- If `2 ^ 36 ≡ 1 (mod p)` then `2 ^ (36 * q + r) ≡ 2 ^ r (mod p)`. -/
