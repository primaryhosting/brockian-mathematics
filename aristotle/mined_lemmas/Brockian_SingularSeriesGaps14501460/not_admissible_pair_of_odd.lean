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

theorem not_admissible_pair_of_odd {d : ℕ} (hd : Odd d) :
    ¬ Admissible ({0, (d : ℤ)} : Finset ℤ) := by
  intro h
  obtain ⟨r, hr2, hr⟩ := h 2 Nat.prime_two
  obtain ⟨k, hk⟩ := hd
  interval_cases r
  · exact hr 0 (by simp) (by simp)
  · refine hr (d : ℤ) (by simp) ?_
    rw [hk]
    push_cast
    omega

/-- Admissibility of the pair `{0, d}` is exactly evenness of the gap `d`. -/
