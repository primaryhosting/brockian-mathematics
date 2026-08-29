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

theorem spectralParameter_isReal_of_hasBrockianWitness
    {s : ℂ} (h : HasBrockianWitness s) : (spectralParameter s).im = 0 := by
  obtain ⟨H, _, _, T, v, hT, hv, hTv⟩ := h
  have h1 : conj (spectralParameter s) = spectralParameter s :=
    symmetric_eigenvalue_isReal hT hv hTv
  have h2 := congrArg Complex.im h1
  simp only [Complex.conj_im] at h2
  linarith

/-- The spectral parameter of `s` is real exactly when `s` lies on the critical line. -/
