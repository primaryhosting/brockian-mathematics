/-!
# Gram Nonneg
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.BaezDuarte.gram_nonneg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Riemann.BaezDuarte

open scoped InnerProductSpace BigOperators

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The Gram form of a finite family of vectors in a real inner product space is
nonnegative: it is the squared norm of the corresponding linear combination. -/

theorem gram_nonneg_two_of_gram (a b : ℝ) :
    0 ≤ ∑ i : Fin 2, ∑ j : Fin 2,
      (![a, b] i) * (![a, b] j) * (inner (![(1 : ℝ), -1] i) (![(1 : ℝ), -1] j) : ℝ) :=
  gram_nonneg _ _

end Riemann.BaezDuarte

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

