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

import Mathlib

/-!
# RH Of Brockian System
Category: Brockian (Open Discharge)
Target: Brockian.RiemannScaffold.RH_of_BrockianSystem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian
namespace RiemannScaffold

open Complex

/-- The Riemann Hypothesis, in the form: every zero of `riemannZeta` lying in the
right half-plane `0 < Re s` lies on the critical line `Re s = 1 / 2`.

(Since `riemannZeta` has no zeros with `Re s ≥ 1`, this is the usual statement that
every nontrivial zero lies on the critical line.) -/

theorem zeta_ne_zero (B : BrockianSystem) {s : ℂ} (h1 : 1 / 2 < s.re) (h2 : s.re < 1) :
    riemannZeta s ≠ 0 := by
  rw [← B.exp_brockLog s h1 h2]
  exact Complex.exp_ne_zero _

end BrockianSystem

/-- **The Riemann Hypothesis holds for any Brockian system.**

Given a Brockian system (a logarithm of `ζ` on the right half of the critical strip),
every zero of `riemannZeta` with positive real part lies on the critical line.

The three regimes are handled separately: `Re s ≥ 1` by the classical nonvanishing of `ζ`
there, `1/2 < Re s < 1` by the Brockian system itself, and `0 < Re s < 1/2` by reflecting
through the functional equation. -/
