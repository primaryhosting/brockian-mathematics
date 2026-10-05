/-
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder
open scoped MatrixOrder

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
# Choi–Jamiołkowski

This file develops, for linear maps `Φ : Mₘ(ℂ) →ₗ[ℂ] Mₙ(ℂ)`, the equivalence between

* complete positivity of `Φ` (every ampliation `Φ ⊗ id_k` preserves positive semidefiniteness),
* positive semidefiniteness of the Choi matrix `C(Φ)`,
* existence of a Kraus (operator sum) representation of `Φ`.
-/

namespace QI

open Matrix

variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- The Choi matrix of a linear map `Φ : Mₘ(ℂ) →ₗ[ℂ] Mₙ(ℂ)`, given by
`C_{(i,a),(j,b)} = (Φ Eᵢⱼ)_{a b}` where `Eᵢⱼ` are the matrix units. -/

lemma ampliation_maxEnt (Φ : Matrix m m ℂ →ₗ[ℂ] Matrix n n ℂ) :
    ampliation Φ m maxEnt = (choiMatrix Φ).submatrix Prod.swap Prod.swap := by
  ext p q
  have h : (Matrix.of fun i j => (maxEnt : Matrix (m × m) (m × m) ℂ) (i, p.2) (j, q.2)) =
      Matrix.single p.2 q.2 (1 : ℂ) := by
    ext i j
    rw [Matrix.of_apply, maxEnt_apply, Matrix.single_apply]
    by_cases h1 : i = p.2 <;> by_cases h2 : j = q.2 <;>
      simp [h1, h2, eq_comm, and_comm]
  simp [ampliation, choiMatrix, Matrix.submatrix_apply, h]

omit [Fintype n] [DecidableEq n] in
