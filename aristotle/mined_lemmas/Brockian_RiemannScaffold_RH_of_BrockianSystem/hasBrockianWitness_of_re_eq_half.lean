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

theorem hasBrockianWitness_of_re_eq_half {s : ℂ} (hs : s.re = 1 / 2) :
    HasBrockianWitness s := by
  refine ⟨ℂ, inferInstance, inferInstance, spectralParameter s • LinearMap.id, 1,
    ?_, one_ne_zero, ?_⟩
  · intro x y
    have hre : conj (spectralParameter s) = spectralParameter s := by
      apply Complex.conj_eq_iff_im.mpr
      rw [spectralParameter_im, hs]
      ring
    simp only [LinearMap.smul_apply, LinearMap.id_coe, id_eq, inner_smul_left, inner_smul_right,
      hre]
  · simp

/-- The Brockian (Hilbert–Pólya) hypothesis is equivalent to the Riemann Hypothesis. -/
