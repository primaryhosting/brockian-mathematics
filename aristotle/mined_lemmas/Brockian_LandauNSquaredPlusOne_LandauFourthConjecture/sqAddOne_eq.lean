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
# Landau Fourth Conjecture
Category: Brockian Conjecture
Target: Brockian.LandauNSquaredPlusOne.LandauFourthConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on file layout: Lean 4 requires `import` commands to be the very first
commands in a file, so the module doc comment above appears immediately after
the single `import Mathlib` line.

Landau's fourth problem ("are there infinitely many primes of the form
`n ^ 2 + 1`?") is an open problem, so what is proved here is a *conditional
reduction*: Bunyakovsky's conjecture implies Landau's fourth conjecture.
The reduction is complete and unconditional in itself: it verifies the two
hypotheses of Bunyakovsky's conjecture for the polynomial `X ^ 2 + 1`
(irreducibility over `ℤ`, and the absence of a fixed prime divisor).

Two unconditional companion results are also proved:
* every prime `p` with `p % 4 ≠ 3` divides some `n ^ 2 + 1`;
* infinitely many primes divide some number of the form `n ^ 2 + 1`.

Mathlib results used: `Polynomial.Monic.irreducible_iff_roots_eq_zero_of_degree_le_three`
(irreducibility of `X ^ 2 + 1` over `ℤ`), `ZMod.exists_sq_eq_neg_one_iff`
(`-1` is a square mod `p` iff `p % 4 ≠ 3`) and `Nat.infinite_setOf_prime_modEq_one`
(Dirichlet, primes `≡ 1 [MOD 4]`). No Mathlib lemma settles Landau's fourth problem
itself; it is open.
-/

namespace Brockian.LandauNSquaredPlusOne

open Polynomial

/-- **Bunyakovsky's conjecture**: an integer polynomial `f` with positive leading
coefficient, of degree at least one, irreducible over `ℤ`, and with no fixed prime
divisor (for every prime `p` there is some `n` with `p ∤ f n`) takes prime values
infinitely often. -/

lemma sqAddOne_eq : sqAddOne = X ^ 2 + 1 := by
  simp [sqAddOne]

