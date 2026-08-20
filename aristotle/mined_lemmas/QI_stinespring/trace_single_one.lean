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

private lemma trace_single_one (a a' : A) :
    (Matrix.single a' a (1 : ℂ)).trace = if a = a' then 1 else 0 := by
  simp [Matrix.trace, Matrix.diag, Matrix.single_apply, ite_and, Finset.sum_ite_eq]

omit [Fintype A] [DecidableEq A] in
/-- Sanity check: the identity channel is completely positive. -/
