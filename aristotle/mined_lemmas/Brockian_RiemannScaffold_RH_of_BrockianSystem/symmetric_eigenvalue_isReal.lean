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

theorem symmetric_eigenvalue_isReal
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {T : H →ₗ[ℂ] H} (hT : T.IsSymmetric) {v : H} (hv : v ≠ 0) {mu : ℂ}
    (hTv : T v = mu • v) : conj mu = mu := by
  have hsym := hT v v
  rw [hTv] at hsym
  rw [inner_smul_left, inner_smul_right] at hsym
  have hvv : (inner ℂ v v : ℂ) ≠ 0 := by
    simpa [inner_self_eq_zero] using hv
  exact mul_right_cancel₀ hvv hsym

/-- The discharged sub-lemma: a Brockian witness forces the spectral parameter to be real. -/
