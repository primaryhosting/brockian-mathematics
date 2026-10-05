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
# Ruth Aaron Infinitude
Category: Brockian Conjecture
Target: Brockian.RuthAaronPairs.RuthAaronInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
A *Ruth–Aaron pair* is a pair of consecutive integers `(n, n+1)` whose sums of prime
factors, counted with multiplicity, agree; the name comes from the pair `(714, 715)`.
Whether there are infinitely many such pairs is an open problem (Erdős); the file below
develops the basic theory of the function `sopfr`, proves a number of unconditional
structural results about Ruth–Aaron pairs, and gives the infinitude statement as a
conditional reduction from the unboundedness hypothesis.
-/

namespace Brockian
namespace RuthAaronPairs

/-! ## The sum-of-prime-factors function `sopfr` -/

/-- `sopfr n` is the sum of the prime factors of `n`, counted with multiplicity
(OEIS A001414).  By convention `sopfr 0 = sopfr 1 = 0`. -/

lemma sopfr_list_prod : ∀ L : List ℕ, (∀ p ∈ L, p.Prime) → sopfr L.prod = L.sum
  | [], _ => by simp
  | a :: L, h => by
      have ha : a.Prime := h a (List.mem_cons_self ..)
      have hL : ∀ p ∈ L, p.Prime := fun x hx => h x (List.mem_cons_of_mem _ hx)
      have hprod : L.prod ≠ 0 := by
        rcases eq_or_ne L [] with rfl | hne
        · simp
        · have := (list_sum_le_prod L (fun x hx => (hL x hx).two_le)).2 hne
          omega
      simp only [List.prod_cons, List.sum_cons]
      rw [sopfr_mul ha.ne_zero hprod, sopfr_prime ha, sopfr_list_prod L hL]

/-- Convenient computation rule: if `n` is the product of the list of primes `L`,
then `sopfr n` is the sum of `L`. -/
