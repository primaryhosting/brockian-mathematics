import Mathlib

/-!
# Holevo Bound
Category: Frontier Qi
Target: QI.holevo_bound
Statement: Accessible information about a quantum ensemble is at most its Holevo χ quantity.
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

set_option grind.warning false

namespace QI

open Finset

/-! ### Classical entropies -/

/-- Shannon entropy of a probability vector, in nats. -/

lemma sum_smul_commutingState {ι : Type*} [Fintype ι] (U : Matrix n n ℂ)
    (p : ι → ℝ) (r : ι → n → ℝ) :
    (∑ i, (p i : ℂ) • commutingState U (r i))
      = commutingState U (fun z => ∑ j, p j * r j z) := by
  simp only [commutingState]
  rw [← sum_smul_diagState p r, Matrix.mul_sum, Matrix.sum_mul]
  exact Finset.sum_congr rfl (fun i _ => by simp)

