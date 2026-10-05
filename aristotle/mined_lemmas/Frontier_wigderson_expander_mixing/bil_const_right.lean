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

/-- The bilinear form `u ↦ v ↦ ∑ᵢ ∑ⱼ uᵢ Mᵢⱼ vⱼ` attached to a matrix `M`. -/

lemma bil_const_right {d : ℝ} (hrow : ∀ i, ∑ j, M i j = d) (u : V → ℝ) (c : ℝ) :
    bil M u (fun _ => c) = c * d * ∑ i, u i := by
  unfold bil
  have h : ∀ i : V, ∑ j, u i * M i j * c = c * d * u i := by
    intro i
    have : ∑ j, u i * M i j * c = (∑ j, M i j) * (u i * c) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [this, hrow i]; ring
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => h i), ← Finset.mul_sum]

/-- If all column sums of `M` equal `d`, then `bil M 1 v = d * ∑ v`. -/
