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

lemma bil_shift {A : Matrix (Fin n) (Fin n) ℝ} (hsymm : A.IsSymm) {d : ℝ}
    (hreg : ∀ i, ∑ j, A i j = d) (x y : Fin n → ℝ) (a b : ℝ) :
    bil A (fun i => x i + a) (fun j => y j + b)
      = bil A x y + b * d * (∑ i, x i) + a * d * (∑ j, y j) + a * b * d * n := by
  rw [bil_add_left, bil_add_right, bil_add_right, bil_const_right hreg,
    bil_const_left hsymm hreg, bil_const_right hreg]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- The number of edges between `S` and `T` as a value of the bilinear form. -/
