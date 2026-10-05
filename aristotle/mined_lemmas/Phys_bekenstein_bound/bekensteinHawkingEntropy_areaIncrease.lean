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

theorem bekensteinHawkingEntropy_areaIncrease
    (k R E hbar c G : ℝ) (hc : c ≠ 0) (hhbar : hbar ≠ 0) (hG : G ≠ 0) :
    bekensteinHawkingEntropy k (8 * Real.pi * G * E * R / c ^ 4) hbar c G
      = bekensteinBoundValue k R E hbar c := by
  unfold bekensteinHawkingEntropy bekensteinBoundValue
  field_simp
  ring

/--
**The Bekenstein bound.**

For a physical system of total energy `E` contained in a sphere of radius `R`, the
thermodynamic entropy `S` satisfies
`S ≤ 2 π k R E / (ℏ c)`.

The statement is proved from the standard physical inputs of Bekenstein's
gedankenexperiment, supplied as hypotheses:

* `hArea` : lowering the system into a black hole raises the horizon area by
  `ΔA = 8 π G E R / c⁴` (Geroch process);
* `hEntropy` : the black hole entropy gain is the Bekenstein–Hawking entropy
  `k c³ ΔA / (4 G ℏ)` of that area increase;
* `hGSL` : the generalized second law — the entropy `S` lost from the exterior does not
  exceed the entropy `ΔS` gained by the black hole.

Together with `c ≠ 0`, `ℏ ≠ 0`, `G ≠ 0` these force the bound.
-/
