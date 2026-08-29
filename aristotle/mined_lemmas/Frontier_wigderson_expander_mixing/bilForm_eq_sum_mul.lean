/-
# Wigderson Expander Mixing
Category: Frontier Abel
Target: Frontier.wigderson_expander_mixing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Wigderson Expander Mixing
Category: Frontier Abel
Target: Frontier.wigderson_expander_mixing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

variable {V : Type*} [Fintype V]

/-- The bilinear form `xᵀ A y` associated to a "weight matrix" `A : V → V → ℝ`. -/

lemma bilForm_eq_sum_mul (A : V → V → ℝ) (x y : V → ℝ) :
    bilForm A x y = ∑ i, x i * ∑ j, A i j * y j := by
  simp only [bilForm, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

