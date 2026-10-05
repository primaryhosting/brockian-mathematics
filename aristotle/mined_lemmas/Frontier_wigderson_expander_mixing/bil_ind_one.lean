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

lemma bil_ind_one {A : V → V → ℝ} {d : ℝ} (hreg : ∀ i, ∑ j, A i j = d) (S : Finset V) :
    bil A (indf S) onev = d * (S.card : ℝ) := by
  have inner : ∀ i : V, ∑ j, indf S i * A i j * onev j = d * indf S i := by
    intro i
    simp only [onev, mul_one, ← Finset.mul_sum, hreg i]
    ring
  simp only [bil, inner, ← Finset.mul_sum, sum_indf]

