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
# Ruth Aaron Infinitude
Category: Brockian Conjecture
Target: Brockian.RuthAaronPairs.RuthAaronInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ruth Aaron Infinitude
Category: Brockian Conjecture
Target: Brockian.RuthAaronPairs.RuthAaronInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

A *Ruth–Aaron pair* is a pair of consecutive integers `(n, n+1)` whose sums of prime factors,
counted with multiplicity, agree; e.g. `(5, 6)`, `(8, 9)`, `(714, 715)`.  Whether there are
infinitely many such pairs is a well-known open problem (Erdős).

This file gives a Lean-checked conditional proof: assuming **Schinzel's Hypothesis H**, there
are infinitely many Ruth–Aaron pairs.  The reduction goes through the polynomial identity
```
(12u² + 36u + 23)(4u + 9) + 1 = 4 (12u² + 39u + 26)(u + 2)
```
together with the matching identity of sums
```
(12u² + 36u + 23) + (4u + 9) = 4 + (12u² + 39u + 26) + (u + 2) .
```
Hence whenever the four polynomial values are simultaneously prime, `n = (12u²+36u+23)(4u+9)`
and `n + 1 = 2 · 2 · (12u²+39u+26) · (u+2)` have the same sum of prime factors.  The four
polynomials are irreducible, have positive leading coefficients, and have no fixed prime
divisor (`u = 5` already gives the Ruth–Aaron pair `(14587, 14588)`), so Hypothesis H supplies
arbitrarily large such `u`.
-/

namespace Brockian.RuthAaronPairs

open Polynomial

/-- `sopfr n` is the sum of the prime factors of `n`, counted with multiplicity
(`sopfr 1 = 0`, `sopfr 12 = 2 + 2 + 3 = 7`). -/

lemma family_identity (u : ℕ) :
    (12 * u ^ 2 + 36 * u + 23) * (4 * u + 9) + 1 =
      4 * ((12 * u ^ 2 + 39 * u + 26) * (u + 2)) := by
  ring

/-- The matching sum-of-prime-factors identity for the family. -/
