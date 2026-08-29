/-
# Holevo Bound
Category: Frontier Qi
Target: QI.holevo_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Holevo Bound
Category: Frontier Qi
Target: QI.holevo_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QI

open Matrix Finset ComplexOrder

/-! ## Classical information quantities -/

variable {ι X I Y : Type*}

/-- Shannon entropy of a finite (sub)probability vector, `H(p) = -∑ p i log (p i)`. -/

lemma isHermitian_unitary_conj_diagonal (U : Matrix n n ℂ) (d : n → ℝ) :
    (U * diagonal (fun i => (d i : ℂ)) * star U).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    (isHermitian_diagonal_real d).eq, ← Matrix.star_eq_conjTranspose, mul_assoc]

/-- The von Neumann entropy of a unitary conjugate of a real diagonal matrix is the Shannon
entropy of the diagonal. -/
