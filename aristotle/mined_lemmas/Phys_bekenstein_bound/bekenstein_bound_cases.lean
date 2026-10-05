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
