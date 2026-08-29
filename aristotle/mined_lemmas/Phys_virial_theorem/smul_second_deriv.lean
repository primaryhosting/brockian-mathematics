/-!
# Virial Theorem
Category: Frontier Phys
Target: Phys.virial_theorem
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

open MeasureTheory Filter Topology
open RealInnerProductSpace

namespace Phys

section Virial

/-!
We work with a one–dimensional quantum system on the line.

* `u : ℝ → ℂ` is the wave function of a bound stationary state, `u'` its derivative and
  `u''` its second derivative.
* `V : ℝ → ℝ` is the potential and `V'` its derivative (so `x * V' x` is `r · ∇V`).
* `c = ℏ² / (2m) ` is the kinetic coefficient, so that the Hamiltonian is
  `H ψ = -c ψ'' + V ψ` and the stationary Schrödinger equation reads `H u = E u`.

The kinetic energy expectation value is `⟨T⟩ = ∫ ⟪u x, (-c) * u'' x⟫` (real inner product on
`ℂ`, i.e. the real part of the usual Hermitian pairing), and the virial expectation value is
`⟨r · ∇V⟩ = ∫ x * V' x * ‖u x‖²`.
-/

variable {c E : ℝ} {u u' u'' : ℝ → ℂ} {V V' : ℝ → ℝ}

/-- The Schrödinger equation `-c u'' + V u = E u`, rewritten as `c • u'' = (V - E) • u`. -/

private lemma smul_second_deriv
    (hSch : ∀ x, -(c : ℂ) * u'' x + (V x : ℂ) * u x = (E : ℂ) * u x) (x : ℝ) :
    c • u'' x = (V x - E) • u x := by
  have h : (c : ℂ) * u'' x = ((V x - E : ℝ) : ℂ) * u x := by
    push_cast
    linear_combination -(hSch x)
  rw [Complex.real_smul, Complex.real_smul]
  exact h

/-- `c ⟪u, u''⟫ = (V - E) ‖u‖²`. -/
