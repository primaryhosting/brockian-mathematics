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

private lemma hasDerivAt_virialAux
    (hu : ∀ x, HasDerivAt u (u' x) x) (hu' : ∀ x, HasDerivAt u' (u'' x) x)
    (hV : ∀ x, HasDerivAt V (V' x) x)
    (hSch : ∀ x, -(c : ℂ) * u'' x + (V x : ℂ) * u x = (E : ℂ) * u x) (x : ℝ) :
    HasDerivAt (virialAux c E u u' V)
      (2 * c * ‖u' x‖ ^ 2 - x * V' x * ‖u x‖ ^ 2) x := by
  have hK := (hasDerivAt_normSq_deriv hu' x).const_mul c
  have hN := hasDerivAt_normSq hu x
  have hVE : HasDerivAt (fun t => (V t - E) * ‖u t‖ ^ 2)
      (V' x * ‖u x‖ ^ 2 + (V x - E) * (2 * ⟪u x, u' x⟫)) x := ((hV x).sub_const E).mul hN
  have hF := hK.sub hVE
  have hxF := (hasDerivAt_id x).mul hF
  have hP := (hasDerivAt_inner_u_u' hu hu' x).const_mul c
  have h := hxF.add hP
  have hA := inner_u_u'' hSch x
  have hB := inner_u'_u'' hSch x
  convert h using 1
  simp only [id_eq]
  linear_combination (-(2 : ℝ) * x) * hB - hA

/-- The auxiliary function vanishes at infinity for a bound state. -/
