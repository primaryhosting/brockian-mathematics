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

/-
# RH Of Brockian System
Category: Brockian (Open Discharge)
Target: Brockian.RiemannScaffold.RH_of_BrockianSystem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# RH Of Brockian System
Category: Brockian (Open Discharge)
Target: Brockian.RiemannScaffold.RH_of_BrockianSystem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped ComplexConjugate

set_option maxHeartbeats 1000000

namespace Brockian
namespace RiemannScaffold

/-- The nontrivial zeros of the Riemann zeta function: zeros inside the critical strip. -/

theorem RH_of_BrockianSystem (hB : BrockianSystem) :
    ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2 := by
  intro s hz h0 h1
  have hw : HasBrockianWitness s := hB s ⟨hz, h0, h1⟩
  have him := spectralParameter_isReal_of_hasBrockianWitness hw
  rw [spectralParameter_im] at him
  linarith

/-- Conversely, every point of the critical line admits a Brockian witness (multiplication by a
real scalar on `ℂ`), so the Brockian hypothesis is consistent and is exactly equivalent to RH. -/
