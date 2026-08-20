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

noncomputable def nu (H : Finset ℤ) (p : ℕ) : ℕ :=
  ((Finset.range p).filter (fun r : ℕ => ∃ x ∈ H, ((p : ℤ) ∣ (x - (r : ℤ))))).card

/-- The local factor at the prime `p` of the Hardy–Littlewood singular series of `H`,
namely `(1 - ν_H(p)/p) * (1 - 1/p)^{-|H|}`. -/
