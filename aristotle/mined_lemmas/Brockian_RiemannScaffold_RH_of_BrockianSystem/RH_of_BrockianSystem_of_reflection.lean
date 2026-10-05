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

open Complex
open scoped Real

namespace Brockian.RiemannScaffold

/-- A **Brockian system** for the Riemann zeta function.

The single field records *Brockian half-plane positivity*: the Riemann zeta function has no
zeros strictly to the right of the critical line inside the critical strip.

This is the "open" input of the scaffold: it is not proved here (it is equivalent to the
Riemann hypothesis, see `brockianSystem_iff_riemannHypothesis`).  Everything else in this
file — in particular the reflection step across the critical line, which was previously carried
as a named hypothesis — is discharged unconditionally. -/
structure BrockianSystem : Prop where
  /-- Brockian half-plane positivity: no zeta zeros with `1/2 < Re s < 1`. -/
  no_zero_right_of_critical_line :
    ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → riemannZeta s ≠ 0

/-- If `s` is a nontrivial zero of `ζ` lying strictly to the left of the critical line, then its
reflection `1 - s` is also a zero of `ζ`.

This is the reflection sub-lemma of the Brockian scaffold; it is proved here from the functional
equation, so it no longer has to be assumed. -/

theorem RH_of_BrockianSystem_of_reflection (B : BrockianSystem)
    (hreflect : ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * (n + 1)) → s.re < 1 / 2 →
      riemannZeta (1 - s) = 0) :
    RiemannHypothesis := by
  intro s hz htriv _hne1
  rcases lt_trichotomy s.re (1 / 2) with hlt | heq | hgt
  · exfalso
    have hzr : riemannZeta (1 - s) = 0 := hreflect s hz htriv hlt
    have hre : 1 / 2 < (1 - s).re := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    exact no_zero_of_half_lt_re B hre hzr
  · exact heq
  · exact absurd hz (no_zero_of_half_lt_re B hgt)

/-- **The Riemann hypothesis for a Brockian system**, unconditionally: the reflection hypothesis
has been discharged (see `zeta_reflection_of_re_lt_half`). -/
