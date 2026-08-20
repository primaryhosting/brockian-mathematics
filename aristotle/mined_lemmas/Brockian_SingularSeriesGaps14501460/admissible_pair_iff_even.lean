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

theorem admissible_pair_iff_even (d : ℕ) :
    Admissible ({0, (d : ℤ)} : Finset ℤ) ↔ Even d := by
  constructor
  · intro h
    by_contra hodd
    exact not_admissible_pair_of_odd (Nat.odd_iff.mpr (Nat.not_even_iff.mp hodd)) h
  · exact admissible_pair_of_even

/-- **The admissible gap range 1450–1460.**
Among the gaps `d` with `1450 ≤ d ≤ 1460`, the admissible ones (i.e. those for which the
pair `{0, d}` is an admissible tuple) are exactly `1450, 1452, 1454, 1456, 1458, 1460`;
and for each such gap every truncation of the Hardy–Littlewood singular series of `{0, d}`
is positive. -/
