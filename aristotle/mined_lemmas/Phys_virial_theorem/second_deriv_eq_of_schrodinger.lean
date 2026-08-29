import Mathlib

/-!
# Virial Theorem
Category: Frontier Phys
Target: Phys.virial_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


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

open MeasureTheory Filter Topology

/-- The (unnormalized) kinetic energy density `ψ* (T ψ)` of a one-dimensional
wave function `ψ` with second derivative `ψ2`, for a particle of mass `m`
(in units with `ℏ = 1`), i.e. `T = -(1/2m) d²/dx²`. -/

theorem second_deriv_eq_of_schrodinger {m E : ℝ} (hm : m ≠ 0) {V : ℝ → ℝ} {ψ ψ2 : ℝ → ℂ}
    (hSch : ∀ x, -(1 / (2 * m)) * ψ2 x + ((V x : ℝ) : ℂ) * ψ x = (E : ℂ) * ψ x) :
    ∀ x, ψ2 x = 2 * (m : ℂ) * (((V x : ℝ) : ℂ) - (E : ℂ)) * ψ x := by
  intro x
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  have h := hSch x
  field_simp at h
  linear_combination -h

/-- The key pointwise identity: the derivative of the virial boundary flux equals
`2 * (kinetic density) - (virial density)`. -/
