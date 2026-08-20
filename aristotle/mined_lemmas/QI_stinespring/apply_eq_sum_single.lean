import Mathlib
/-!
# Stinespring
Category: Frontier Qi
Target: QI.stinespring
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder
open scoped MatrixOrder

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

open Matrix

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The partial trace over the second (ancilla) factor of a matrix indexed by a product. -/

lemma apply_eq_sum_single (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) (ρ : Matrix n n ℂ)
    (i j : m) :
    Φ ρ i j = ∑ a : n, ∑ b : n, ρ a b * (Φ (Matrix.single a b 1)) i j := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single ρ]
  simp only [map_sum, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [show Matrix.single a b (ρ a b) = (ρ a b) • Matrix.single a b (1 : ℂ) by
    rw [Matrix.smul_single]; simp, map_smul]
  simp

/-- The Choi matrix of `Φ`. -/
