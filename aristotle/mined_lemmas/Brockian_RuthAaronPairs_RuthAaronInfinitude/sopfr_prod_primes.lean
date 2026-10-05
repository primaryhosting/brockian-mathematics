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

lemma sopfr_prod_primes : ∀ l : List ℕ, (∀ p ∈ l, Nat.Prime p) → sopfr l.prod = l.sum
  | [], _ => by simp
  | p :: l, h => by
      have hp : Nat.Prime p := h p (by simp)
      have hl : ∀ q ∈ l, Nat.Prime q := fun q hq => h q (by simp [hq])
      have hprod : l.prod ≠ 0 := by
        refine List.prod_ne_zero ?_
        intro h0
        exact (hl 0 h0).ne_zero rfl
      simp only [List.prod_cons, List.sum_cons]
      rw [sopfr_mul hp.ne_zero hprod, sopfr_prime hp, sopfr_prod_primes l hl]

/-! ## Small Ruth–Aaron pairs -/

