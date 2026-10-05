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

lemma bil_one_ind {A : V → V → ℝ} {d : ℝ} (hcol : ∀ j, ∑ i, A i j = d) (T : Finset V) :
    bil A onev (indf T) = d * (T.card : ℝ) := by
  have inner : ∀ i : V, ∑ j, onev i * A i j * indf T j = ∑ j ∈ T, A i j := by
    intro i
    have : ∀ j : V, onev i * A i j = A i j := by intro j; simp [onev]
    simp only [this]
    exact sum_indicator_mul T (fun j => A i j)
  simp only [bil, inner]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun j _ => hcol j)]
  simp [mul_comm]

