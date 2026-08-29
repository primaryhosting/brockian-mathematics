/-
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is a plain comment because Lean requires `import` lines to
-- precede any module docstring; the same text is repeated verbatim below.)
import Mathlib

/-!
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QI

open Matrix Finset
open scoped ComplexOrder MatrixOrder

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The Choi matrix of a linear map `Φ : Mₙ(ℂ) →ₗ Mₘ(ℂ)`:
`C (i,k) (j,l) = (Φ Eᵢⱼ) k l`, where the `Eᵢⱼ` are the matrix units. -/

theorem isCompletelyPositive_of_hasKrausDecomposition (h : HasKrausDecomposition Φ) :
    IsCompletelyPositive Φ := by
  obtain ⟨N, V, hV⟩ := h
  intro d _ A hA
  classical
  have key : ampliation Φ d A =
      ∑ a : Fin N, (Matrix.of fun (x : m × d) (y : n × d) =>
        V a x.1 y.1 * (if x.2 = y.2 then 1 else 0)) * A *
        (Matrix.of fun (x : m × d) (y : n × d) =>
          V a x.1 y.1 * (if x.2 = y.2 then 1 else 0))ᴴ := by
    ext x y
    simp only [ampliation, Matrix.of_apply, hV, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [kron_conj_apply]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Finset.sum_mul,
      mul_assoc]
    exact Finset.sum_comm
  rw [key]
  refine posSemidef_sum Finset.univ fun a _ => ?_
  have := hA.conjTranspose_mul_mul_same
    ((Matrix.of fun (x : m × d) (y : n × d) => V a x.1 y.1 * (if x.2 = y.2 then 1 else 0))ᴴ)
  simpa using this

/-- If the Choi matrix of `Φ` is positive semidefinite, then `Φ` has a Kraus decomposition. -/
