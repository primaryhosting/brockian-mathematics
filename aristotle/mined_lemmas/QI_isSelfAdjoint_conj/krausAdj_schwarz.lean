import Mathlib

/-!
# Quantum relative entropy and data processing

This file develops, for finite-dimensional systems (complex matrices), the basic theory of the
Umegaki quantum relative entropy

`D(ρ‖σ) = Tr(ρ log ρ) - Tr(ρ log σ)`

for faithful (positive definite) density matrices, together with

* Klein's inequality `QI.relEntropy_nonneg` : `0 ≤ D(ρ‖σ)`;
* invariance under unitary channels `QI.relEntropy_unitary_conj`;
* the data-processing inequality `QI.data_processing_condExp` for trace-self-adjoint maps fixing `σ`
  (conditional expectations), and its concrete instance for the completely dephasing channel
  `QI.data_processing_dephasing`.
-/

open Matrix
open scoped ComplexOrder

namespace QI

universe u

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- The logarithm of a (Hermitian) matrix, defined through the continuous functional calculus. -/

theorem krausAdj_schwarz {ι : Type u} [Fintype ι] {K : ι → Matrix m n ℂ}
    (hK : ∑ a, (K a)ᴴ * K a = 1) (Y : Matrix m m ℂ) :
    (krausAdj K (Yᴴ * Y) - (krausAdj K Y)ᴴ * krausAdj K Y).PosSemidef := by
  set R := krausAdj K Y with hR
  have h2 : ∑ a, (K a)ᴴ * Y * K a = R := rfl
  have h1 : ∑ a, (K a)ᴴ * Yᴴ * K a = Rᴴ := by rw [hR, krausAdj_conjTranspose]; rfl
  have h3 : krausAdj K (Yᴴ * Y) = ∑ a, (K a)ᴴ * (Yᴴ * Y) * K a := rfl
  have key : krausAdj K (Yᴴ * Y) - Rᴴ * R
      = ∑ a, (Y * K a - K a * R)ᴴ * (Y * K a - K a * R) := by
    have expand : ∀ a : ι, (Y * K a - K a * R)ᴴ * (Y * K a - K a * R)
        = (K a)ᴴ * (Yᴴ * Y) * K a - ((K a)ᴴ * Yᴴ * K a) * R - Rᴴ * ((K a)ᴴ * Y * K a)
          + Rᴴ * ((K a)ᴴ * K a) * R := by
      intro a
      simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
        Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
      abel
    rw [Finset.sum_congr rfl fun a _ => expand a]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
    rw [h1, h2, hK, Matrix.mul_one, h3]
    abel
  rw [key]
  exact Matrix.posSemidef_sum _ fun a _ => Matrix.posSemidef_conjTranspose_mul_self _

/-! ### The Sylvester equation `t • P W + W Q = P - Q` -/

/-- The solution of the Sylvester equation `t • (P * W) + W * Q = D`, written in terms of a pair
of diagonalising unitaries. -/
