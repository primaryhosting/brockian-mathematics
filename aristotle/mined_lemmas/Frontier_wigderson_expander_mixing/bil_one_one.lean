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

lemma bil_one_one {A : V → V → ℝ} {d : ℝ} (hreg : ∀ i, ∑ j, A i j = d) :
    bil A (onev : V → ℝ) onev = d * (Fintype.card V : ℝ) := by
  have inner : ∀ i : V, ∑ j, onev i * A i j * onev j = d := by
    intro i
    have : ∀ j : V, (onev : V → ℝ) i * A i j * onev j = A i j := by
      intro j; simp [onev]
    simp only [this]
    exact hreg i
  simp only [bil, inner]
  simp [Finset.card_univ, mul_comm]

/-! ### Centred indicator vectors -/

/-- The indicator vector of `S`, centred so as to be orthogonal to the all-ones vector. -/
