import Mathlib
/-!
# Stinespring
Category: Frontier Qi
Target: QI.stinespring
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder MatrixOrder

namespace QI

variable {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- The partial trace over the second (environment) tensor factor. -/

private lemma trace_mul_single (M : Matrix A A ℂ) (a a' : A) :
    (M * Matrix.single a' a 1).trace = M a a' := by
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.single_apply, ite_and,
    Finset.sum_ite_eq]

