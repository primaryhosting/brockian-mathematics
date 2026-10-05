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

-- (Lean requires `import` before any command, including a module docstring, so the header
-- above is repeated verbatim as the module docstring immediately after the import.)

import Mathlib

/-!
# Ruth Aaron Infinitude
Category: Brockian Conjecture
Target: Brockian.RuthAaronPairs.RuthAaronInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.RuthAaronPairs

/-! ## The sum-of-prime-factors function -/

/-- `sopfr n` is the sum of the prime factors of `n`, counted with multiplicity
(`sopfr 0 = sopfr 1 = 0`). -/

def admissibleParams : Set ℕ :=
  {k : ℕ | Nat.Prime (k + 1) ∧ Nat.Prime (4 * k + 5) ∧ Nat.Prime (12 * k ^ 2 + 15 * k + 1) ∧
    Nat.Prime (12 * k ^ 2 + 12 * k + 1)}

/-- A Schinzel/Bateman–Horn-type hypothesis: the four irreducible integer polynomials
`k + 1`, `4 * k + 5`, `12 * k ^ 2 + 15 * k + 1`, `12 * k ^ 2 + 12 * k + 1`
are simultaneously prime for infinitely many `k`.  (Smallest witnesses: `k = 2`, giving the
Ruth–Aaron pair `948 = 2 ^ 2 * 3 * 79`, `949 = 13 * 73`, and `k = 42`, giving
`3749428 = 2 ^ 2 * 43 * 21799`, `3749429 = 173 * 21673`.) -/
