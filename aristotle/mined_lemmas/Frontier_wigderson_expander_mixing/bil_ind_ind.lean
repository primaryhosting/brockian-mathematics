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

section

variable {V : Type*} [Fintype V]

/-- The bilinear form `xᵀ A y` associated to a weight matrix `A`. -/

lemma bil_ind_ind (A : V → V → ℝ) (S T : Finset V) :
    bil A (indf S) (indf T) = ∑ i ∈ S, ∑ j ∈ T, A i j := by
  have inner : ∀ i : V, ∑ j, indf S i * A i j * indf T j = (∑ j ∈ T, A i j) * indf S i := by
    intro i
    calc ∑ j, indf S i * A i j * indf T j
        = ∑ j ∈ T, indf S i * A i j := sum_indicator_mul T (fun j => indf S i * A i j)
      _ = (∑ j ∈ T, A i j) * indf S i := by rw [← Finset.mul_sum]; ring
  simp only [bil, inner]
  exact sum_indicator_mul S (fun i => ∑ j ∈ T, A i j)

