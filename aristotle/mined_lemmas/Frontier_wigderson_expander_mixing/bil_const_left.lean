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

lemma bil_const_left {d : ℝ} (hcol : ∀ j, ∑ i, M i j = d) (v : V → ℝ) (c : ℝ) :
    bil M (fun _ => c) v = c * d * ∑ j, v j := by
  unfold bil
  rw [Finset.sum_comm]
  have h : ∀ j : V, ∑ i, c * M i j * v j = c * d * v j := by
    intro j
    have : ∑ i, c * M i j * v j = (∑ i, M i j) * (c * v j) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [this, hcol j]; ring
  rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => h j), ← Finset.mul_sum]

end

/-- Indicator sums: `∑ᵢ 1_S(i) f i = ∑_{i ∈ S} f i`. -/
