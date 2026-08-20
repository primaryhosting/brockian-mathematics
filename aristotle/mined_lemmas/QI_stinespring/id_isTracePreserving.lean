/-
# Stinespring
Category: Frontier Qi
Target: QI.stinespring
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Stinespring
Category: Frontier Qi
Target: QI.stinespring
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Finite-dimensional Stinespring dilation theorem: every completely positive
trace-preserving (CPTP) linear map on matrix algebras can be realised by
adjoining an ancilla in a fixed pure state, applying a unitary on the enlarged
system, and tracing out the environment.

The main result is `QI.stinespring`. Along the way we prove Choi's theorem
(`QI.choi_posSemidef`), the Kraus decomposition of a completely positive map
(`QI.exists_kraus`), the completeness relation for the Kraus operators of a
trace-preserving map (`QI.kraus_sum_eq_one`), and the extension of an isometry
to a unitary (`QI.exists_unitary_extension`).
-/

open Matrix
open scoped Kronecker ComplexOrder

namespace QI

variable {A B : Type*}

/-- The partial trace of a matrix on a bipartite system `B ⊗ E` over the second
(environment) factor. -/

lemma id_isTracePreserving [Fintype A] :
    IsTracePreserving (LinearMap.id : Matrix A A ℂ →ₗ[ℂ] Matrix A A ℂ) := fun _ => rfl

end QI

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

