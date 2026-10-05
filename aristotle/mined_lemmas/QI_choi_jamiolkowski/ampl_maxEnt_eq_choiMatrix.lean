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

lemma ampl_maxEnt_eq_choiMatrix (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) :
    ampl n Φ (maxEnt n) = choiMatrix Φ := by
  ext p q
  have h : (Matrix.of fun i j => maxEnt n (p.1, i) (q.1, j)) = Matrix.single p.1 q.1 (1 : ℂ) := by
    ext i j
    simp [maxEnt, Matrix.single_apply]
  simp [ampl, choiMatrix, h]

omit [Fintype m] [DecidableEq m] in
/-- A completely positive map has positive semidefinite Choi matrix. -/
