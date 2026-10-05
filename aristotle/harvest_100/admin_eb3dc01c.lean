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
noncomputable def bekensteinBoundValue (k R E hbar c : ℝ) : ℝ :=
  2 * Real.pi * k * R * E / (hbar * c)

/-- The Bekenstein–Hawking entropy `k c³ A / (4 G ℏ)` of a black hole of horizon
area `A`. -/
noncomputable def bekensteinHawkingEntropy (k A hbar c G : ℝ) : ℝ :=
  k * c ^ 3 * A / (4 * G * hbar)

/-- Geroch-process step: the horizon-area increase `ΔA = 8 π G E R / c⁴` produced by
lowering a body of energy `E` and radius `R` into a black hole contributes exactly the
Bekenstein bound to the black hole entropy. -/
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
theorem bekenstein_bound
    (k R E hbar c G S ΔA ΔS : ℝ)
    (hc : c ≠ 0) (hhbar : hbar ≠ 0) (hG : G ≠ 0)
    (hArea : ΔA = 8 * Real.pi * G * E * R / c ^ 4)
    (hEntropy : ΔS = bekensteinHawkingEntropy k ΔA hbar c G)
    (hGSL : S ≤ ΔS) :
    S ≤ bekensteinBoundValue k R E hbar c := by
  subst hArea
  subst hEntropy
  rwa [bekensteinHawkingEntropy_areaIncrease k R E hbar c G hc hhbar hG] at hGSL

/-- Explicit form of the Bekenstein bound: under the same physical inputs,
`S ≤ 2 π k R E / (ℏ c)`. -/
theorem bekenstein_bound_explicit
    (k R E hbar c G S ΔA ΔS : ℝ)
    (hc : c ≠ 0) (hhbar : hbar ≠ 0) (hG : G ≠ 0)
    (hArea : ΔA = 8 * Real.pi * G * E * R / c ^ 4)
    (hEntropy : ΔS = k * c ^ 3 * ΔA / (4 * G * hbar))
    (hGSL : S ≤ ΔS) :
    S ≤ 2 * Real.pi * k * R * E / (hbar * c) :=
  bekenstein_bound k R E hbar c G S ΔA ΔS hc hhbar hG hArea hEntropy hGSL

/-- The bound is nonnegative for physically sensible data: nonnegative Boltzmann
constant, radius and energy, and positive `ℏ` and `c`. -/
theorem bekensteinBoundValue_nonneg
    (k R E hbar c : ℝ) (hk : 0 ≤ k) (hR : 0 ≤ R) (hE : 0 ≤ E)
    (hhbar : 0 < hbar) (hc : 0 < c) :
    0 ≤ bekensteinBoundValue k R E hbar c := by
  unfold bekensteinBoundValue
  positivity

/-- Version of the Bekenstein bound that splits on the relevant hypothesis: either the
generalized second law is invoked (`S ≤ ΔS`), or the system carries no positive entropy
at all and the bound is nonnegative. -/
theorem bekenstein_bound_cases
    (k R E hbar c G S ΔA ΔS : ℝ)
    (hc : c ≠ 0) (hhbar : hbar ≠ 0) (hG : G ≠ 0)
    (hArea : ΔA = 8 * Real.pi * G * E * R / c ^ 4)
    (hEntropy : ΔS = bekensteinHawkingEntropy k ΔA hbar c G)
    (hcases : S ≤ ΔS ∨ (S ≤ 0 ∧ 0 ≤ bekensteinBoundValue k R E hbar c)) :
    S ≤ bekensteinBoundValue k R E hbar c := by
  rcases hcases with hGSL | ⟨hS, hB⟩
  · exact bekenstein_bound k R E hbar c G S ΔA ΔS hc hhbar hG hArea hEntropy hGSL
  · exact hS.trans hB

/-- A Schwarzschild black hole saturates the Bekenstein bound: taking `R` to be its
Schwarzschild radius `2 G M / c²`, `E = M c²` its total energy and `A = 4 π R²` its
horizon area, the Bekenstein–Hawking entropy equals `2 π k R E / (ℏ c)` exactly. -/
theorem bekensteinHawkingEntropy_eq_bound_schwarzschild
    (k M hbar c G R E A : ℝ)
    (hR : R = 2 * G * M / c ^ 2) (hE : E = M * c ^ 2) (hA : A = 4 * Real.pi * R ^ 2) :
    bekensteinHawkingEntropy k A hbar c G = bekensteinBoundValue k R E hbar c := by
  subst hA
  subst hE
  subst hR
  unfold bekensteinHawkingEntropy bekensteinBoundValue
  field_simp

end Phys

