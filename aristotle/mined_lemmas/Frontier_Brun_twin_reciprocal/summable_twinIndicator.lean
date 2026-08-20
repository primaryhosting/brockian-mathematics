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

theorem summable_twinIndicator
    (h : Summable (fun m : ℕ => (twinCount (2 ^ (m + 1)) : ℝ) / 2 ^ m)) :
    Summable twinIndicator := by
  have hnn : ∀ m : ℕ, 0 ≤ (twinCount (2 ^ (m + 1)) : ℝ) / 2 ^ m := by
    intro m; positivity
  refine summable_of_sum_range_le twinIndicator_nonneg (c := ∑' m, (twinCount (2 ^ (m + 1)) : ℝ) / 2 ^ m) ?_
  intro K
  have hK : K ≤ 2 ^ K := Nat.le_of_lt (Nat.lt_two_pow_self)
  have h1 : ∑ n ∈ range K, twinIndicator n ≤ ∑ n ∈ range (2 ^ K), twinIndicator n := by
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (fun x hx => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hK)) ?_
    intro n _ _
    exact twinIndicator_nonneg n
  have h2 := sum_range_two_pow_twinIndicator_le K
  have h3 : ∑ m ∈ range K, (twinCount (2 ^ (m + 1)) : ℝ) / 2 ^ m
      ≤ ∑' m, (twinCount (2 ^ (m + 1)) : ℝ) / 2 ^ m :=
    Summable.sum_le_tsum _ (fun i _ => hnn i) h
  linarith

end Brun

import RequestProject.Brun.Sieve

/-!
# Choosing the sieve parameters

With `N = 2^m`, sieve level `z = 2^q` and truncation level `k = 20 ℓ` where `ℓ = log₂ m` and
`q = m / (40 ℓ)`, Brun's sieve bound gives
`twinCount (2^m) / 2^m = O(√m / m²)`, which is summable.
-/

set_option maxHeartbeats 2000000

namespace Brun

open Finset Filter

/-! ### Elementary growth lemmas -/

