/-
# Landauer Principle
Category: Frontier Phys
Target: Phys.landauer_principle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Phys

open Finset

/-- Shannon entropy (in nats) of a finite probability distribution `p`. -/

theorem landauer_principle_sharp (k T : ℝ) (hk : 0 < k) (hT : 0 < T) :
    ∃ Q σ : ℝ, 0 ≤ σ ∧
      σ = (shannonEntropy erasedBit - shannonEntropy uniformBit) + Q / (k * T) ∧
      Q = k * T * Real.log 2 := by
  refine ⟨k * T * Real.log 2, 0, le_refl 0, ?_, rfl⟩
  have hkT : (k * T) ≠ 0 := ne_of_gt (mul_pos hk hT)
  field_simp
  rw [shannonEntropy_erasedBit, shannonEntropy_uniformBit]
  ring

end Phys

