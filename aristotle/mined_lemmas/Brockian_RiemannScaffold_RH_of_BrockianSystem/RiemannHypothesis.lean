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

def RiemannHypothesis : Prop :=
  ∀ s : ℂ, 0 < s.re → riemannZeta s = 0 → s.re = 1 / 2

/-- A **Brockian system** for the Riemann zeta function: a function `brockLog` which
exponentiates to `riemannZeta` on the right half `{1/2 < Re s < 1}` of the critical
strip, i.e. a (not necessarily continuous) choice of logarithm of `ζ` there. -/
structure BrockianSystem where
  /-- The Brockian logarithm attached to the system. -/
  brockLog : ℂ → ℂ
  /-- `brockLog` is a logarithm of `riemannZeta` on the right half of the critical strip. -/
  exp_brockLog : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → Complex.exp (brockLog s) = riemannZeta s

namespace BrockianSystem

/-- A Brockian system forces `riemannZeta` to be nonvanishing on the right half of the
critical strip, since the complex exponential is nowhere zero. -/
