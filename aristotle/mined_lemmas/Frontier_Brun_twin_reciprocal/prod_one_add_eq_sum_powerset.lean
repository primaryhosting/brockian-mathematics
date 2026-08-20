import Mathlib
import RequestProject.Brun.Final

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

/-- **Brun's theorem**: the sum of the reciprocals of the twin primes converges.

The twin primes are indexed by the subtype of naturals `p` such that both `p` and `p + 2`
are prime, and the summand is `1 / p`. -/

lemma prod_one_add_eq_sum_powerset (P : Finset ℕ) (a : ℕ → ℝ) :
    ∏ p ∈ P, (1 + a p) = ∑ S ∈ P.powerset, ∏ p ∈ S, a p := by
  have := Finset.prod_add a (fun _ => (1 : ℝ)) P
  simp only [Finset.prod_const_one, mul_one] at this
  rw [← this]
  exact Finset.prod_congr rfl (fun p _ => by ring)

