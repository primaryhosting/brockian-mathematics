import Mathlib
/-!
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators MatrixOrder
open Matrix ComplexOrder

namespace QI

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The amplification `id_k ⊗ Φ` of a linear map `Φ` between matrix algebras:
its `((a, p), (b, q))` entry is the `(p, q)` entry of `Φ` applied to the `(a, b)` block. -/

lemma cp_of_hasKraus {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ} (h : HasKraus Φ) :
    IsCompletelyPositive Φ := by
  obtain ⟨ι, hι, K, hK⟩ := h
  intro k _ X hX
  classical
  have hsum : ampl k Φ X
      = ∑ a, (Matrix.of fun (u : k × m) (v : k × n) => if u.1 = v.1 then K a u.2 v.2 else 0) * X
          * (Matrix.of fun (u : k × m) (v : k × n) => if u.1 = v.1 then K a u.2 v.2 else 0)ᴴ := by
    ext p q
    simp only [ampl, hK, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.of_apply, Fintype.sum_prod_type, apply_ite (star : ℂ → ℂ), star_zero, ite_mul,
      zero_mul, mul_ite, mul_zero]
    refine Finset.sum_congr rfl fun a _ => ?_
    conv_rhs => rw [Finset.sum_comm]
    simp
  rw [hsum]
  refine Finset.sum_induction _ _ (fun _ _ => Matrix.PosSemidef.add) Matrix.PosSemidef.zero ?_
  intro a _
  exact hX.mul_mul_conjTranspose_same _

/-- **Choi–Jamiołkowski isomorphism**: a linear map between matrix algebras is completely
positive if and only if its Choi matrix is positive semidefinite. -/
