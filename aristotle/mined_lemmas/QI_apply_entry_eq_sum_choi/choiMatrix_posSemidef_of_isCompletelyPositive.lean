import Mathlib

/-!
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder
open Matrix

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

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The amplification `id_p ⊗ Φ` of a linear map `Φ` between matrix algebras:
a `(p × n)`-matrix is viewed as a `p × p` block matrix of `n × n` blocks, and `Φ`
is applied to each block. -/

lemma choiMatrix_posSemidef_of_isCompletelyPositive (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ)
    (h : IsCompletelyPositive Φ) : (choiMatrix Φ).PosSemidef := by
  set w : (n × n) → ℂ := fun x => if x.1 = x.2 then (1 : ℂ) else 0 with hw
  set Ω : Matrix (n × n) (n × n) ℂ := Matrix.of fun x y => w x * w y with hΩdef
  have hΩ : Ω.PosSemidef := by
    have hfac : Ω = (Matrix.of fun (_ : Unit) (x : n × n) => w x)ᴴ *
        (Matrix.of fun (_ : Unit) (x : n × n) => w x) := by
      ext x y
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
        Finset.univ_unique, Finset.sum_singleton, hΩdef]
      have : star (w x) = w x := by
        simp only [hw]
        split <;> simp
      rw [this]
    rw [hfac]
    exact Matrix.posSemidef_conjTranspose_mul_self _
  have hEq : amplify Φ n Ω = choiMatrix Φ := by
    ext x y
    have hblock : (Matrix.of fun i j => Ω (x.1, i) (y.1, j)) = Matrix.single x.1 y.1 (1 : ℂ) := by
      ext i j
      simp only [Matrix.of_apply, hΩdef, hw, Matrix.single]
      by_cases hi : x.1 = i <;> by_cases hj : y.1 = j <;> simp [hi, hj]
    simp only [amplify, choiMatrix, Matrix.of_apply, hblock]
  exact hEq ▸ h n Ω hΩ

/-- **Choi–Jamiołkowski isomorphism**: a linear map between matrix algebras is completely
positive if and only if its Choi matrix is positive semidefinite. -/
