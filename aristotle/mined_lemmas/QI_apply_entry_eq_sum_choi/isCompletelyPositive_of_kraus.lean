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

lemma isCompletelyPositive_of_kraus {ι : Type} [Fintype ι]
    (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) (V : ι → Matrix m n ℂ)
    (hV : ∀ X : Matrix n n ℂ, Φ X = ∑ s : ι, V s * X * (V s)ᴴ) :
    IsCompletelyPositive Φ := by
  intro p _ _ A hA
  classical
  set W : ι → Matrix (p × m) (p × n) ℂ :=
    fun s => Matrix.of fun x y => if x.1 = y.1 then V s x.2 y.2 else 0 with hW
  have key : amplify Φ p A = ∑ s : ι, W s * A * (W s)ᴴ := by
    ext x y
    simp only [amplify, Matrix.of_apply, hV, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun s _ => ?_
    have e1 : ∀ v : p × n, ∑ u : p × n, W s x u * A u v
        = ∑ i : n, V s x.2 i * A (x.1, i) v := by
      intro v
      rw [Fintype.sum_prod_type]
      simp only [hW, Matrix.of_apply, ite_mul, zero_mul]
      rw [Finset.sum_eq_single x.1]
      · simp
      · intro c _ hc
        simp [Ne.symm hc]
      · intro hc
        exact absurd (Finset.mem_univ x.1) hc
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, e1]
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single y.1]
    · refine Finset.sum_congr rfl fun j _ => ?_
      simp only [hW, Matrix.of_apply]
      rfl
    · intro d _ hd
      refine Finset.sum_eq_zero fun j _ => ?_
      simp [hW, Ne.symm hd]
    · intro hd
      exact absurd (Finset.mem_univ y.1) hd
  rw [key]
  refine Finset.sum_induction _ _ (fun a b ha hb => ha.add hb) Matrix.PosSemidef.zero ?_
  intro s _
  exact hA.mul_mul_conjTranspose_same (W s)

open scoped MatrixOrder in
/-- Key intermediate step: if the Choi matrix of `Φ` is positive semidefinite, then `Φ`
admits a Kraus representation `Φ X = ∑ s, V s * X * (V s)ᴴ`. -/
