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
# Sixth Unitary Perfect Exists
Category: Brockian Conjecture
Target: Brockian.UnitaryPerfect.SixthUnitaryPerfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sixth Unitary Perfect Exists
Category: Brockian Conjecture
Target: Brockian.UnitaryPerfect.SixthUnitaryPerfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.UnitaryPerfect

/-! ## Unitary divisors and the unitary divisor sum -/

/-- The unitary divisors of `n`: the divisors `d` of `n` with `gcd d (n / d) = 1`. -/

private theorem coprime_list_prod {a : ℕ} :
    ∀ (l : List ℕ), (∀ b ∈ l, Nat.Coprime a b) → Nat.Coprime a l.prod
  | [], _ => by simp
  | b :: l, h => by
      rw [List.prod_cons]
      exact Nat.Coprime.mul_right (h b (by simp))
        (coprime_list_prod l fun c hc => h c (by simp [hc]))

/-- `σ*` of a product of a pairwise coprime list of prime powers is the product of the
`1 + p ^ k`. -/
