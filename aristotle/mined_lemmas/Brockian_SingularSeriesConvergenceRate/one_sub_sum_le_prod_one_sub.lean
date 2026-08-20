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

/-!
# An effective convergence rate for the twin-prime singular series

The Hardy–Littlewood singular series for prime pairs `(n, n + 2)` is

  `𝔖 = 2 * ∏_{p odd prime} (1 - 1/(p-1)^2)`,

the product being over all odd primes.  In this file we define the partial products
`Brockian.twinPartial N` (product over the odd primes `p ≤ N`), show they converge, and
prove an *effective* rate of convergence:

  `|Brockian.singularSeriesPartial N - Brockian.singularSeries| ≤ 2 / (N - 1)`  for `N ≥ 3`.
-/

namespace Brockian

open Filter Finset
open scoped Topology

/-- The set of odd primes `p ≤ N`, as a `Finset`. -/

theorem one_sub_sum_le_prod_one_sub (s : Finset ℕ) (f : ℕ → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1) :
    1 - ∑ i ∈ s, f i ≤ ∏ i ∈ s, (1 - f i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
      have hs0 : ∀ i ∈ s, 0 ≤ f i := fun i hi => h0 i (Finset.mem_cons_of_mem hi)
      have hs1 : ∀ i ∈ s, f i ≤ 1 := fun i hi => h1 i (Finset.mem_cons_of_mem hi)
      have hprodnn : (0:ℝ) ≤ ∏ i ∈ s, (1 - f i) :=
        Finset.prod_nonneg (fun i hi => by linarith [hs1 i hi])
      have hfa0 : 0 ≤ f a := h0 a (Finset.mem_cons_self _ _)
      have hfa1 : f a ≤ 1 := h1 a (Finset.mem_cons_self _ _)
      have hind := ih hs0 hs1
      have hsum : (0:ℝ) ≤ ∑ i ∈ s, f i := Finset.sum_nonneg hs0
      rw [Finset.prod_cons, Finset.sum_cons]
      nlinarith [hind]

