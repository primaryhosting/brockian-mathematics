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

theorem isRuthAaronPair_948 : IsRuthAaronPair 948 := by
  refine ⟨by norm_num, ?_⟩
  have h1 : (948 : ℕ) = [2, 2, 3, 79].prod := by norm_num
  have h2 : (948 + 1 : ℕ) = [13, 73].prod := by norm_num
  rw [h2, h1, sopfr_prod_primes _ (by intro p hp; fin_cases hp <;> norm_num),
    sopfr_prod_primes _ (by intro p hp; fin_cases hp <;> norm_num)]
  norm_num

/-! ## A parametric family of Ruth–Aaron pairs

For every `k` one has the polynomial identity

`4 * (k + 1) * (12 * k ^ 2 + 15 * k + 1) + 1 = (4 * k + 5) * (12 * k ^ 2 + 12 * k + 1)`

and the two sides have matching sums of prime factors as soon as `k + 1`, `4 * k + 5`,
`12 * k ^ 2 + 15 * k + 1` and `12 * k ^ 2 + 12 * k + 1` are all prime, because

`4 + (k + 1) + (12 * k ^ 2 + 15 * k + 1) = (4 * k + 5) + (12 * k ^ 2 + 12 * k + 1)`.
-/

/-- The candidate Ruth–Aaron number attached to a parameter `k`. -/
