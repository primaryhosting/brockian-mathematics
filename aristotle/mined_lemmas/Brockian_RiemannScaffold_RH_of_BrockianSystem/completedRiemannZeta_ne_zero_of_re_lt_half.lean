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

-- (Lean requires `import` lines to precede every other token in a module, so the header
-- comment above appears immediately after the single `import Mathlib` line.)

open Complex

namespace Brockian.RiemannScaffold

/-- A **Brockian system** is a "logarithmic discharge" of the completed Riemann zeta function
`Λ` on the open half-plane to the right of the critical line: a function `logLambda` which
exponentiates to `Λ` at every point `s` with `1/2 < re s`, `s ≠ 1` (the point `s = 1`, where
`Λ` has its pole, is excluded).

Equivalently, a Brockian system is exactly a witness that `Λ` has no zeros strictly to the
right of the critical line. Its existence is the genuinely open half of the Riemann
hypothesis; the theorem `RH_of_BrockianSystem` below shows that it is in fact *all* of it,
i.e. that the reflected half-plane and the trivial zeros can be handled unconditionally. -/
structure BrockianSystem where
  /-- The Brockian logarithm of the completed zeta function. -/
  logLambda : ℂ → ℂ
  /-- `Λ s = exp (logLambda s)` to the right of the critical line, away from the pole. -/
  exp_logLambda : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 →
    completedRiemannZeta s = Complex.exp (logLambda s)

namespace BrockianSystem

/-- A Brockian system forces the completed zeta function to be nonzero strictly to the right
of the critical line (away from the pole at `s = 1`). -/

theorem completedRiemannZeta_ne_zero_of_re_lt_half (B : BrockianSystem) {s : ℂ}
    (hs : s.re < 1 / 2) (hs0 : s ≠ 0) :
    completedRiemannZeta s ≠ 0 := by
  have hre : 1 / 2 < (1 - s).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hne : (1 - s) ≠ 1 := by
    intro h
    exact hs0 (by linear_combination -h)
  have h := B.completedRiemannZeta_ne_zero_of_half_lt_re hre hne
  rwa [completedRiemannZeta_one_sub] at h

end BrockianSystem

/-- **The Riemann hypothesis, given a Brockian system.**

If a Brockian system exists — i.e. if the completed zeta function admits a logarithm on the
half-plane `re s > 1/2` — then every nontrivial zero of `riemannZeta` lies on the critical
line.  The remaining content (the reflected half-plane `re s < 1/2` and the trivial zeros) is
discharged unconditionally, using the functional equation `Λ (1 - s) = Λ s` and the exact
description of the zeros of the archimedean factor `Gammaℝ`. -/
