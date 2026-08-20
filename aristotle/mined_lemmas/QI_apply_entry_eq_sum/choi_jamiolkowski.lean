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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QI

open Matrix
open scoped ComplexOrder

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The Choi matrix of a linear map `Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ`.
It is the block matrix `∑ i j, Eᵢⱼ ⊗ Φ Eᵢⱼ`, written entrywise as
`choiMatrix Φ (i, a) (j, b) = Φ (single i j 1) a b`. -/

theorem choi_jamiolkowski (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) :
    IsCompletelyPositive Φ ↔ (choiMatrix Φ).PosSemidef := by
  constructor
  · intro hCP
    have h := hCP n _ posSemidef_maxEntangled
    have hEq : choiMatrix Φ =
        (Matrix.of fun p q : m × n => Φ (Matrix.of fun i j =>
          (if i = p.2 then (1 : ℂ) else 0) * (if j = q.2 then (1 : ℂ) else 0)) p.1 q.1).submatrix
          Prod.swap Prod.swap := by
      ext p q
      have hsingle : ∀ s t : n, (Matrix.of fun i j : n =>
          (if i = s then (1 : ℂ) else 0) * (if j = t then (1 : ℂ) else 0))
          = Matrix.single s t 1 := by
        intro s t
        ext i j
        simp only [Matrix.of_apply, Matrix.single_apply, ite_and]
        by_cases hi : i = s
        · by_cases hj : j = t
          · simp [hi, hj]
          · simp [hi, hj, Ne.symm hj]
        · by_cases hj : j = t <;> simp [hi, hj, Ne.symm hi]
      simp only [choiMatrix, Matrix.submatrix_apply, Matrix.of_apply,
        Prod.fst_swap, Prod.snd_swap, hsingle]
    rw [hEq]
    exact h.submatrix _
  · intro h
    obtain ⟨N, K, hK⟩ := exists_kraus_of_choiMatrix_posSemidef Φ h
    exact isCompletelyPositive_of_kraus Φ K hK

end QI

#print axioms QI.choi_jamiolkowski

