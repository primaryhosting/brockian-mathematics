import Mathlib
import Brockian.RiemannScaffold

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
#print axioms Brockian.RiemannScaffold.RH_of_BrockianSystem
#print axioms Brockian.RiemannScaffold.nonempty_brockianSystem_iff_RH

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

open scoped ComplexConjugate InnerProductSpace

noncomputable section

namespace Brockian
namespace RiemannScaffold

/-! ## The Brockian system and the critical-line theorem -/

/-- A *nontrivial zero* of the Riemann zeta function: a zero lying in the open critical
strip `0 < Re s < 1`. -/

def brockianBasis : Module.Basis ZeroIdx ℂ BrockianSpace :=
  Module.Basis.span orthonormal_zeroBasisVec.linearIndependent

