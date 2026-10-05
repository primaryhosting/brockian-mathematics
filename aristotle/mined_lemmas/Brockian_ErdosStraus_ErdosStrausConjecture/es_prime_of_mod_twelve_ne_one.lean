import Brockian.ErdosStraus

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
# Erdos Straus Conjecture
Category: Brockian Conjecture
Target: Brockian.ErdosStraus.ErdosStrausConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.ErdosStraus

/-- `ES n` says that `4 / n` is a sum of three positive unit fractions
(the Erdős–Straus property for `n`; the denominators need not be distinct). -/

theorem es_prime_of_mod_twelve_ne_one {p : ℕ} (hp : p.Prime) (h : p % 12 ≠ 1) : ES p :=
  es_of_mod_twelve_ne_one hp.two_le h

/-- **Conditional Erdős–Straus conjecture.**
If every prime `p ≡ 1 (mod 12)` satisfies the Erdős–Straus property, then every integer
`n ≥ 2` does, i.e. the full Erdős–Straus conjecture holds.
(The Erdős–Straus conjecture is an open problem; this is a Lean-checked reduction of it
to the single residue class `p ≡ 1 (mod 12)` of primes.) -/
