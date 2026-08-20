import Mathlib

/-!
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Statement: CP maps correspond to positive Choi matrices (Choi–Jamiołkowski isomorphism).
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
open scoped MatrixOrder

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The Choi matrix of a linear map `Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ`:
the block matrix whose `(a, b)` block is `Φ (single a b 1)`, i.e.
`Choi Φ = (id ⊗ Φ) (|Ω⟩⟨Ω|)` for the unnormalised maximally entangled vector `Ω`. -/

lemma ampliation_posSemidef_of_kraus (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ)
    (V : (n × m) → Matrix m n ℂ) (hV : ∀ X : Matrix n n ℂ, Φ X = ∑ c, V c * X * (V c)ᴴ) :
    IsCompletelyPositive Φ := by
  intro k _ _ A hA
  set W : (n × m) → Matrix (k × m) (k × n) ℂ :=
    fun c => Matrix.of fun x y => if x.1 = y.1 then V c x.2 y.2 else 0 with hW
  have key : ampliation Φ k A = ∑ c, W c * A * (W c)ᴴ := by
    ext p q
    simp only [ampliation, Matrix.of_apply, hV, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [hW, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Fintype.sum_prod_type, ite_mul, zero_mul, mul_ite, mul_zero, apply_ite (star : ℂ → ℂ),
      star_zero]
    have h1 : ∀ (x : k) (x1 : n) (x2 : k),
        (∑ x3, if p.1 = x2 then V c p.2 x3 * A (x2, x3) (x, x1) else 0) =
          if p.1 = x2 then ∑ x3, V c p.2 x3 * A (x2, x3) (x, x1) else 0 := by
      intro x x1 x2; split_ifs <;> simp
    simp only [h1, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have h2 : ∀ x : k,
        (∑ x1, if q.1 = x then (∑ x3, V c p.2 x3 * A (p.1, x3) (x, x1)) * star (V c q.2 x1)
          else 0) =
          if q.1 = x then ∑ x1, (∑ x3, V c p.2 x3 * A (p.1, x3) (x, x1)) * star (V c q.2 x1)
          else 0 := by
      intro x; split_ifs <;> simp
    simp only [h2, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [key]
  exact Finset.sum_induction _ _ (fun _ _ h1 h2 => h1.add h2) Matrix.PosSemidef.zero
    (fun c _ => hA.mul_mul_conjTranspose_same (W c))

/-- **Choi–Jamiołkowski isomorphism**: a linear map between matrix algebras is completely
positive if and only if its Choi matrix is positive semidefinite. -/
