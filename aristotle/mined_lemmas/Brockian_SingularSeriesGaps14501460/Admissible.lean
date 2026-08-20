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

def Admissible (H : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ℕ, r < p ∧ ∀ x ∈ H, ¬ ((p : ℤ) ∣ (x - (r : ℤ)))

/-- `nu H p` is the number of residue classes mod `p` occupied by the elements of `H`. -/
