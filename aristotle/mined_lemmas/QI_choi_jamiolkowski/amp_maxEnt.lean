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

lemma amp_maxEnt (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) :
    amp Φ (maxEnt n) = choiMatrix Φ := by
  ext p q
  have h : (Matrix.of fun i j => maxEnt n (p.1, i) (q.1, j)) = Matrix.single p.1 q.1 1 := by
    ext i j
    simp only [maxEnt, Matrix.single_apply, Matrix.of_apply, ite_and]
    split_ifs with h1 h2 h3 <;> simp_all [eq_comm]
  simp only [amp, choiMatrix, Matrix.of_apply, h]

omit [Fintype m] [DecidableEq m] in
/-- Expansion of `Φ A` via linearity in the standard matrix basis. -/
