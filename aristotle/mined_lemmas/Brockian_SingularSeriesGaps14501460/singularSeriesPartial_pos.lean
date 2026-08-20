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

theorem singularSeriesPartial_pos {H : Finset ℤ} (hH : Admissible H) (N : ℕ) :
    0 < singularSeriesPartial H N := by
  refine Finset.prod_pos ?_
  intro p hp
  exact localFactor_pos hH (Finset.mem_filter.mp hp).2

/-- A gap `d` which is even gives an admissible pair `{0, d}`. -/
