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

namespace Frontier

section Mixing

variable {n : ℕ}

/-- The bilinear form `xᵀ A y` associated with a real matrix `A`. -/

lemma bil_comm {A : Matrix (Fin n) (Fin n) ℝ} (hsymm : A.IsSymm) (x y : Fin n → ℝ) :
    bil A x y = bil A y x := by
  unfold bil
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  have h : A j i = A i j := by
    have := congrFun (congrFun hsymm i) j
    simpa [Matrix.transpose_apply] using this
  rw [h]; ring

/-- Pairing a constant vector on the right. -/
