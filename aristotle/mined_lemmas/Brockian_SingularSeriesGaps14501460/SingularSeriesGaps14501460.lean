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

set_option grind.warning false

namespace Brockian

/-- `H` is an *admissible* tuple of integers: for every prime `p` there is a residue class
mod `p` which is avoided by every element of `H`. -/

theorem SingularSeriesGaps14501460 :
    ((Finset.Icc 1450 1460).filter
        (fun d : ℕ => Admissible ({0, (d : ℤ)} : Finset ℤ))
      = ({1450, 1452, 1454, 1456, 1458, 1460} : Finset ℕ)) ∧
    (∀ d ∈ ({1450, 1452, 1454, 1456, 1458, 1460} : Finset ℕ), ∀ N : ℕ,
      0 < singularSeriesPartial ({0, (d : ℤ)} : Finset ℤ) N) := by
  constructor
  · ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton,
      admissible_pair_iff_even, Nat.even_iff]
    omega
  · intro d hd N
    refine singularSeriesPartial_pos (admissible_pair_of_even ?_) N
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rw [Nat.even_iff]
    omega

end Brockian

