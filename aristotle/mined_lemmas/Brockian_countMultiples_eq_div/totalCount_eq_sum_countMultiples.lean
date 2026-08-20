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
# Equidistribution of multiples, and the reduction of the divisor summatory function
to its main term

This file carries out a "level of distribution" style reduction for the simplest possible
sequence, the sequence of all integers, and deduces from it the leading-order asymptotics of
the divisor summatory function.

For a modulus `q`, the number of `n ∈ [1, N]` lying in the residue class `0 mod q` is
`N / q + O(1)` (`abs_countMultiples_sub_le`).  Summing this equidistribution statement over all
moduli `q ≤ N` (a total error of size `O(N)`, `abs_totalCount_sub_harmonic_le`) turns the
"total" count

  `totalCount N = ∑_{n ≤ N} d(n) = ∑_{q ≤ N} #{n ≤ N : q ∣ n}`

into its main term `N * H_N`, where `H_N` is the `N`-th harmonic number.  Since `H_N ∼ log N`,
this gives the Dirichlet asymptotic

  `∑_{n ≤ N} d(n) ∼ N log N`,

which is the statement `total_over_main_tendsto`.
-/

open Filter Finset
open scoped BigOperators Topology

namespace Brockian
namespace EquidistributionBVReduction

/-- The number of integers `n ∈ [1, N]` that are divisible by `q`, i.e. the number of
elements of `[1, N]` in the residue class `0 mod q`. -/

lemma totalCount_eq_sum_countMultiples (N : ℕ) :
    totalCount N = ∑ q ∈ Finset.Icc 1 N, countMultiples N q := by
  have key : ∀ n ∈ Finset.Icc 1 N, n.divisors = {q ∈ Finset.Icc 1 N | q ∣ n} := by
    intro n hn
    simp only [Finset.mem_Icc] at hn
    ext q
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hdvd, hne⟩
      exact ⟨⟨Nat.pos_of_ne_zero (by rintro rfl; simp at hdvd; omega),
        le_trans (Nat.le_of_dvd (by omega) hdvd) hn.2⟩, hdvd⟩
    · rintro ⟨-, hdvd⟩
      exact ⟨hdvd, by omega⟩
  rw [totalCount, Finset.sum_congr rfl (fun n hn => by rw [key n hn])]
  simp only [countMultiples, Finset.card_filter]
  exact Finset.sum_comm

/-- Summing the equidistribution statement over all moduli `q ≤ N`: the total count agrees
with `N * H_N` up to an error of size at most `N`. -/
