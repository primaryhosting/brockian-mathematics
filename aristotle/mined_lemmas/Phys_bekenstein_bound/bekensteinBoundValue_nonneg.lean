/-
# Bekenstein Bound
Category: Frontier Phys
Target: Phys.bekenstein_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Phys

/-- The Bekenstein bound expression `2 π k R E / (ℏ c)`: the maximal thermodynamic
entropy of a system of total energy `E` that fits inside a sphere of radius `R`,
where `k` is Boltzmann's constant, `hbar` the reduced Planck constant and `c` the
speed of light. -/

theorem bekensteinBoundValue_nonneg
    (k R E hbar c : ℝ) (hk : 0 ≤ k) (hR : 0 ≤ R) (hE : 0 ≤ E)
    (hhbar : 0 < hbar) (hc : 0 < c) :
    0 ≤ bekensteinBoundValue k R E hbar c := by
  unfold bekensteinBoundValue
  positivity

/-- Version of the Bekenstein bound that splits on the relevant hypothesis: either the
generalized second law is invoked (`S ≤ ΔS`), or the system carries no positive entropy
at all and the bound is nonnegative. -/
