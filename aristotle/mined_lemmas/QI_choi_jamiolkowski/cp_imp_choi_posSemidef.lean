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

lemma cp_imp_choi_posSemidef (Φ : Matrix m m ℂ →ₗ[ℂ] Matrix n n ℂ)
    (h : IsCompletelyPositive Φ) : (choiMatrix Φ).PosSemidef := by
  have h1 : (ampliation Φ m (maxEnt : Matrix (m × m) (m × m) ℂ)).PosSemidef :=
    h m maxEnt maxEnt_posSemidef
  rw [ampliation_maxEnt] at h1
  have h2 := h1.submatrix (Prod.swap : m × n → n × m)
  have h3 : ((choiMatrix Φ).submatrix Prod.swap Prod.swap).submatrix
      (Prod.swap : m × n → n × m) Prod.swap = choiMatrix Φ := by
    ext p q
    simp [Matrix.submatrix_apply]
  rwa [h3] at h2

end CPtoChoi

section ChoiToKraus

