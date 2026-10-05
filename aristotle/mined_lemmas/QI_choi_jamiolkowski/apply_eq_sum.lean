import Mathlib

/-!
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped MatrixOrder ComplexOrder

namespace QI

open Matrix

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The ampliation `id_d ⊗ Φ` of a linear map `Φ` between matrix algebras, described
blockwise: the `(a, b)` block of the output is `Φ` applied to the `(a, b)` block of the input. -/

lemma apply_eq_sum (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) (A : Matrix n n ℂ) (s t : m) :
    Φ A s t = ∑ i : n, ∑ j : n, A i j * Φ (Matrix.single i j 1) s t := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single A]
  rw [map_sum]
  simp only [Matrix.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  simp only [Matrix.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : Matrix.single i j (A i j) = A i j • Matrix.single i j (1 : ℂ) := by
    ext a b; simp [Matrix.single_apply]
  rw [this, map_smul]
  simp

omit [DecidableEq n] [DecidableEq m] in
/-- If `Φ` has a Kraus decomposition then it is completely positive. -/
