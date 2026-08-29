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

theorem isRuthAaronPair_familyMember {k : ℕ} (h1 : Nat.Prime (k + 1))
    (h2 : Nat.Prime (4 * k + 5)) (h3 : Nat.Prime (12 * k ^ 2 + 15 * k + 1))
    (h4 : Nat.Prime (12 * k ^ 2 + 12 * k + 1)) : IsRuthAaronPair (familyMember k) := by
  constructor
  · unfold familyMember; nlinarith [sq_nonneg k]
  · have hfour : sopfr 4 = 4 := by
      have h : (4 : ℕ) = [2, 2].prod := by norm_num
      rw [h, sopfr_prod_primes _ (by intro p hp; fin_cases hp <;> norm_num)]
      norm_num
    have hn : sopfr (familyMember k) = 4 + (k + 1) + (12 * k ^ 2 + 15 * k + 1) := by
      unfold familyMember
      rw [show 4 * (k + 1) * (12 * k ^ 2 + 15 * k + 1)
            = 4 * ((k + 1) * (12 * k ^ 2 + 15 * k + 1)) by ring,
        sopfr_mul (by norm_num) (Nat.mul_ne_zero h1.ne_zero h3.ne_zero),
        sopfr_mul h1.ne_zero h3.ne_zero, hfour, sopfr_prime h1, sopfr_prime h3]
      ring
    have hn1 : sopfr (familyMember k + 1) = (4 * k + 5) + (12 * k ^ 2 + 12 * k + 1) := by
      rw [familyMember_succ_eq, sopfr_mul h2.ne_zero h4.ne_zero, sopfr_prime h2, sopfr_prime h4]
    rw [hn, hn1]; ring

