import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian

/-! ## Admissible tuples and the Hardy–Littlewood singular series

A finite set `H` of nonnegative integers is *admissible* if for every prime `p` the
elements of `H` do not cover all residue classes modulo `p`.  Equivalently, every local
factor of the Hardy–Littlewood singular series attached to `H` is positive.

The main result `Brockian.SingularSeriesGaps16021610` determines exactly which `d` in the
range `1602 ≤ d ≤ 1610` occur as the diameter of a (large) admissible tuple: precisely the
even ones, and for each of those we exhibit an explicit admissible tuple with at least
`145` elements whose smallest element is `0` and whose largest element is `d`.
-/

/-- `H` is an admissible tuple: for each prime `p` some residue class mod `p` is missed. -/

lemma tuple_admissible (d : ℕ) (hcard : (tuple d).card ≤ 211) : Admissible (tuple d) := by
  intro p hp
  rcases hp.eq_two_or_odd with hp2 | hodd
  · subst hp2
    refine ⟨1, by norm_num, ?_⟩
    intro x hx
    have := (mem_tuple_iff d x).mp hx
    omega
  · by_cases hlt : p < 212
    · have hmem : p ∈ sievePrimes := (mem_sievePrimes_iff p).mpr ⟨hlt, hp, hodd⟩
      have hp3 : 3 ≤ p := by have := hp.two_le; omega
      refine ⟨avoid d p, by have := avoid_le_two d p; omega, ?_⟩
      intro x hx
      exact ((mem_tuple_iff d x).mp hx).2.2 p hmem
    · exact exists_missing_residue _ _ (by omega)

/-! ### The main theorem -/

/-- **Admissible gap range `1602–1610`.**  For `1602 ≤ d ≤ 1610`, there is an admissible
tuple with at least `145` elements, smallest element `0` and largest element `d` (so of
diameter exactly `d`), all of whose singular series local factors are positive, **iff**
`d` is even.  In particular each of `d = 1602, 1604, 1606, 1608, 1610` is realised as the
diameter of such a tuple, and no odd `d` in this range is. -/
